import MultitapeBatches

/-!
# Complete fixed-control multitape phase compiler

This assembles the expanded tape batches and joint leaf step into the
recursive simulator. Choice bits live in tape stack slots. The control
alphabet, tape count and cell alphabet are fixed independently of time.
All address sequences are computed without inspecting input data.
-/

noncomputable section
namespace MultitapeEfficientPhase
open ObliviousProgram ObliviousCopy ObliviousPhase MultitapeLeaf MultitapeBatches

variable {tapes : ℕ} {State Symbol : Type*}

def instructions (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (topLevel : ℕ) :
    ℕ → ℕ → List (StepInstruction tapes State Symbol)
  | 0, _ => MultitapeLeaf.instructions machine anchor
  | level + 1, nextSlot =>
      compressAll (2 ^ level) (PhaseStack.stackSlot topLevel nextSlot) ++
      instructions machine anchor topLevel level (nextSlot + 1) ++
      compressAll (2 ^ level) (PhaseStack.stackSlot topLevel (nextSlot + 1)) ++
      instructions machine anchor topLevel level (nextSlot + 2) ++
      expandAll (2 ^ level) (PhaseStack.stackSlot topLevel (nextSlot + 1)) ++
      expandAll (2 ^ level) (PhaseStack.stackSlot topLevel nextSlot)

theorem preserves_earlier_slot (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (topLevel level nextSlot oldSlot : ℕ) (hlevel : level ≤ topLevel) (hold : oldSlot < nextSlot)
    (simulator : SimulatorConfiguration tapes State Symbol) (tape : Fin tapes) :
    (run (instructions machine anchor topLevel level nextSlot) simulator).memory
        (tape, Sum.inr (PhaseStack.stackSlot topLevel oldSlot)) =
      simulator.memory (tape, Sum.inr (PhaseStack.stackSlot topLevel oldSlot)) := by
  induction level generalizing nextSlot simulator with
  | zero => exact MultitapeLeaf.instructions_buffer machine anchor simulator tape _
  | succ level ih =>
      have hout := PhaseStack.stackSlot_outside topLevel level oldSlot (by omega)
      have hdiff : PhaseStack.stackSlot topLevel oldSlot ≠ PhaseStack.stackSlot topLevel nextSlot := by
        intro heq
        have h := PhaseStack.stackSlot_injective topLevel heq
        omega
      have hdiff' : PhaseStack.stackSlot topLevel oldSlot ≠ PhaseStack.stackSlot topLevel (nextSlot + 1) := by
        intro heq
        have h := PhaseStack.stackSlot_injective topLevel heq
        omega
      simp only [instructions, run_append]
      rw [expansion_preserves_slot _ _ _ tape _ hout, expansion_preserves_slot _ _ _ tape _ hout,
        ih (nextSlot + 2) (by omega) (by omega), compression_preserves_slot _ _ _ tape _ hout hdiff',
        ih (nextSlot + 1) (by omega) (by omega), compression_preserves_slot _ _ _ tape _ hout hdiff]

set_option maxHeartbeats 1600000 in
/-- The expanded instruction list preserves every source tape and head,
not just a supplied source-output property. -/
theorem phase_represents (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (topLevel level nextSlot : ℕ) (hlevel : level ≤ topLevel)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBounds : ∀ tape, |source.head tape| ≤ (2 ^ level : ℕ)) :
    Represents (machine.phaseExecution level source)
      (run (instructions machine anchor topLevel level nextSlot) simulator) := by
  induction level generalizing nextSlot source simulator with
  | zero => exact MultitapeLeaf.step_correct machine anchor source simulator representation (by simpa using headBounds)
  | succ level ih =>
      let half : ℕ := 2 ^ level
      let firstSlot := PhaseStack.stackSlot topLevel nextSlot
      let secondSlot := PhaseStack.stackSlot topLevel (nextSlot + 1)
      let firstPermutations := MultitapeTuring.compressionPermutations half source.head
      let compressedSource := source.permute firstPermutations
      let firstSource := machine.phaseExecution level compressedSource
      let secondPermutations := MultitapeTuring.compressionPermutations half firstSource.head
      let secondSource := machine.phaseExecution level (firstSource.permute secondPermutations)
      let firstCompression := run (compressAll half firstSlot) simulator
      let firstRun := run (instructions machine anchor topLevel level (nextSlot + 1)) firstCompression
      let secondCompression := run (compressAll half secondSlot) firstRun
      let secondRun := run (instructions machine anchor topLevel level (nextSlot + 2)) secondCompression
      let firstExpansion := run (expandAll half secondSlot) secondRun
      have hfull : ∀ tape, |source.head tape| ≤ 2 * (half : ℤ) := by
        intro tape
        simpa [half, pow_succ, mul_comm] using headBounds tape
      have hcompressed : ∀ tape, |compressedSource.head tape| ≤ (half : ℤ) :=
        MultitapeTuring.compressed_head_bound half source hfull
      have hfirstSource : firstSource = machine.run half compressedSource :=
        machine.phaseExecution_correct level compressedSource hcompressed
      have hfirstHeads : ∀ tape, |firstSource.head tape| ≤ 2 * (half : ℤ) := by
        intro tape
        rw [hfirstSource]
        have h := machine.head_bound_run compressedSource half tape
        have hc := hcompressed tape
        omega
      have hsecondHeads : ∀ tape, |(firstSource.permute secondPermutations).head tape| ≤ (half : ℤ) :=
        MultitapeTuring.compressed_head_bound half firstSource hfirstHeads
      have hfirstCompression := compression_correct half firstSlot source simulator representation hfull
      have hfirstRun : Represents firstSource firstRun :=
        ih (nextSlot + 1) (by omega) compressedSource firstCompression hfirstCompression hcompressed
      have hsecondCompression := compression_correct half secondSlot firstSource firstRun hfirstRun hfirstHeads
      have hsecondRun : Represents secondSource secondRun :=
        ih (nextSlot + 2) (by omega) (firstSource.permute secondPermutations)
          secondCompression hsecondCompression hsecondHeads
      have hout := PhaseStack.stackSlot_outside topLevel level nextSlot (by omega)
      have hdiff : firstSlot ≠ secondSlot := by
        intro heq
        have h := PhaseStack.stackSlot_injective topLevel heq
        omega
      have hfirstChoices : ∀ tape, (firstRun.memory (tape, Sum.inr firstSlot)).2 = decide (source.head tape < 0) := by
        intro tape
        change ((run (instructions machine anchor topLevel level (nextSlot + 1)) firstCompression).memory
          (tape, Sum.inr (PhaseStack.stackSlot topLevel nextSlot))).2 = _
        rw [preserves_earlier_slot machine anchor topLevel level (nextSlot + 1) nextSlot (by omega) (by omega)]
        exact compression_choices half firstSlot source simulator representation hfull tape
      have hsecondChoices : ∀ tape, (secondRun.memory (tape, Sum.inr secondSlot)).2 = decide (firstSource.head tape < 0) := by
        intro tape
        change ((run (instructions machine anchor topLevel level (nextSlot + 2)) secondCompression).memory
          (tape, Sum.inr (PhaseStack.stackSlot topLevel (nextSlot + 1)))).2 = _
        rw [preserves_earlier_slot machine anchor topLevel level (nextSlot + 2) (nextSlot + 1) (by omega) (by omega)]
        exact compression_choices half secondSlot firstSource firstRun hfirstRun hfirstHeads tape
      have hfirstChoicesAfter : ∀ tape, (firstExpansion.memory (tape, Sum.inr firstSlot)).2 = decide (source.head tape < 0) := by
        intro tape
        change ((run (expandAll half secondSlot) secondRun).memory (tape, Sum.inr firstSlot)).2 = _
        rw [expansion_preserves_slot half secondSlot firstSlot tape secondRun hout]
        change ((run (instructions machine anchor topLevel level (nextSlot + 2)) secondCompression).memory
          (tape, Sum.inr (PhaseStack.stackSlot topLevel nextSlot))).2 = _
        rw [preserves_earlier_slot machine anchor topLevel level (nextSlot + 2) nextSlot (by omega) (by omega)]
        change ((run (compressAll half secondSlot) firstRun).memory (tape, Sum.inr firstSlot)).2 = _
        rw [compression_preserves_slot half secondSlot firstSlot tape firstRun hout hdiff]
        exact hfirstChoices tape
      have hfirstExpansion := expansion_correct half secondSlot firstSource.head secondSource secondRun hsecondRun hsecondChoices
      have hfinal := expansion_correct half firstSlot source.head
        (secondSource.permute (fun tape => (secondPermutations tape).symm)) firstExpansion hfirstExpansion hfirstChoicesAfter
      simpa only [instructions, run_append, MultitapeTuring.Machine.phaseExecution] using hfinal

theorem source_run_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (topLevel level nextSlot : ℕ) (hlevel : level ≤ topLevel)
    (source : MultitapeTuring.Configuration tapes State Symbol) (simulator : SimulatorConfiguration tapes State Symbol)
    (representation : Represents source simulator) (headBounds : ∀ tape, |source.head tape| ≤ (2 ^ level : ℕ)) :
    Represents (machine.run (2 ^ level) source) (run (instructions machine anchor topLevel level nextSlot) simulator) := by
  rw [← machine.phaseExecution_correct level source headBounds]
  exact phase_represents machine anchor topLevel level nextSlot hlevel source simulator representation headBounds

theorem instruction_count (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (topLevel level nextSlot : ℕ) :
    (instructions machine anchor topLevel level nextSlot).length + 32 * tapes =
      (208 * tapes * level + 40 * tapes + 1) * 2 ^ level := by
  induction level generalizing nextSlot with
  | zero => simp [instructions, MultitapeLeaf.instruction_count]; ring
  | succ level ih =>
      simp only [instructions, List.length_append, compressAll_length, expandAll_length]
      have hfirst := ih (nextSlot + 1)
      have hsecond := ih (nextSlot + 2)
      rw [pow_succ]
      nlinarith

theorem instruction_count_le (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (topLevel level nextSlot : ℕ) :
    (instructions machine anchor topLevel level nextSlot).length ≤ (248 * tapes + 1) * (level + 1) * 2 ^ level := by
  have h := instruction_count machine anchor topLevel level nextSlot
  have hc : 208 * tapes * level + 40 * tapes + 1 ≤ (248 * tapes + 1) * (level + 1) := by nlinarith
  calc
    _ ≤ (208 * tapes * level + 40 * tapes + 1) * 2 ^ level := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ hc

theorem horizon_instruction_count (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes)
    (steps nextSlot : ℕ) (hsteps : 1 ≤ steps) :
    (instructions machine anchor (horizonLevel steps) (horizonLevel steps) nextSlot).length ≤
      (4 * (248 * tapes + 1)) * steps * (Nat.log 2 steps + 1) := by
  have hcount := instruction_count_le machine anchor (horizonLevel steps) (horizonLevel steps) nextSlot
  have hpower := horizon_at_most_twice steps hsteps
  have hlevel : horizonLevel steps + 1 ≤ 2 * (Nat.log 2 steps + 1) := by unfold horizonLevel; omega
  calc
    _ ≤ (248 * tapes + 1) * (horizonLevel steps + 1) * 2 ^ horizonLevel steps := hcount
    _ ≤ ((248 * tapes + 1) * (2 * (Nat.log 2 steps + 1))) * (2 * steps) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hlevel) hpower
    _ = _ := by ring

def sourceInitial (machine : MultitapeTuring.Machine tapes State Symbol) (tape : Fin tapes → ℤ → Symbol) :
    MultitapeTuring.Configuration tapes State Symbol := ⟨machine.initialState, fun _ => 0, tape⟩

def initialControl (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol) :
    Control (Registers tapes State Symbol) (HeadMarker.Cell Symbol) :=
  ⟨⟨machine.initialState, fun _ => 1, fun _ => blank, fun _ => blank, fun _ => .stay⟩, false, (blank, false)⟩

def initialMemory (blank : Symbol) (tape : Fin tapes → ℤ → Symbol) : Fin tapes × RotationProgram.Address → HeadMarker.Cell Symbol
  | (index, .inl cell) => (tape index cell, decide (cell = 0))
  | (_, .inr _) => (blank, false)

def program (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol) (level : ℕ) :=
  ObliviousCopy.program (instructions machine anchor level level 0) (anchor, Sum.inl 0)
    (initialControl machine blank) (initialMemory blank)

theorem initial_represents (machine : MultitapeTuring.Machine tapes State Symbol) (blank : Symbol)
    (tape : Fin tapes → ℤ → Symbol) :
    Represents (sourceInitial machine tape)
      (⟨initialControl machine blank, initialMemory blank tape⟩ : SimulatorConfiguration tapes State Symbol) :=
  ⟨rfl, fun _ _ => rfl⟩

theorem program_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (tape : Fin tapes → ℤ → Symbol) :
    Represents (machine.run (2 ^ level) (sourceInitial machine tape))
      ((program machine anchor blank level).configurationAt tape (instructions machine anchor level level 0).length) := by
  rw [program, ObliviousCopy.program_complete]
  exact source_run_correct machine anchor level level 0 le_rfl (sourceInitial machine tape)
    _ (initial_represents machine blank tape) (by simp [sourceInitial])

end MultitapeEfficientPhase
