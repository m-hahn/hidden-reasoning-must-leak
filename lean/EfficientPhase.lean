import LeafStep

/-!
# Assembled fixed-control recursive phase programs

The instruction list is constructed from the actual leaf, marker, rotation,
and choice-stack programs. Every address is input-independent. The auxiliary
register type and cell alphabet are fixed once the source machine is fixed;
neither contains a variable-size source tape configuration.
-/

noncomputable section

namespace EfficientPhase

open ObliviousProgram ObliviousCopy RotationProgram ObliviousPhase
open LeafStep

variable {State Symbol : Type*}

abbrev StepInstruction (State Symbol : Type*) :=
  Instruction Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol)

theorem compression_correct (half : ℕ) (source : ObliviousPhase.Configuration State Symbol)
    (simulator : LeafStep.SimulatorConfiguration State Symbol) (representation : LeafStep.Represents source simulator)
    (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    LeafStep.Represents (source.permute (compressionPermutation half source.head))
      (run (CompressedTape.compress half) simulator) := by
  have hhead : TapeRotation.inside (8 * half) source.head :=
    TapeRotation.inside_of_abs_le _ _ (by simp only [Nat.cast_mul, Nat.cast_ofNat]; omega)
  have hmarker : ∀ cell, (simulator.memory (Sum.inl cell)).2 = decide (cell = source.head) := by
    intro cell
    rw [representation.2 cell]
  have hdetect := HeadMarker.detect_correct (8 * half) source.head simulator hhead hmarker
  have hshift : (if decide (source.head < 0) then (half : ℤ) else -(half : ℤ)) =
      compressionShift half source.head := by simp [compressionShift]
  unfold CompressedTape.compress
  rw [run_append, hdetect]
  constructor
  · rw [(rotate_control _ _ _).1]
    exact representation.1
  · intro cell
    rw [rotate_main]
    dsimp only
    rw [hshift, representation.2]
    simp only [ObliviousPhase.Configuration.permute, compressionPermutation]
    congr 1
    simp only [Equiv.symm_apply_eq]

theorem compression_saved_correct (half : ℕ) (slot : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : LeafStep.SimulatorConfiguration State Symbol)
    (representation : LeafStep.Represents source simulator) (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    LeafStep.Represents (source.permute (compressionPermutation half source.head))
      (run (PhaseStack.compressSaved half slot) simulator) := by
  have h := compression_correct half source simulator representation headBound
  unfold PhaseStack.compressSaved
  rw [run_append, run_cons, run_nil, PhaseStack.save_memory]
  exact ⟨h.1, fun cell => by simpa using h.2 cell⟩

theorem compression_saved_choice (half : ℕ) (slot : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : LeafStep.SimulatorConfiguration State Symbol)
    (representation : LeafStep.Represents source simulator) (headBound : |source.head| ≤ 2 * (half : ℤ)) :
    ((run (PhaseStack.compressSaved half slot) simulator).memory (Sum.inr slot)).2 = decide (source.head < 0) := by
  have hhead : TapeRotation.inside (8 * half) source.head :=
    TapeRotation.inside_of_abs_le _ _ (by simp only [Nat.cast_mul, Nat.cast_ofNat]; omega)
  have hmarker : ∀ cell, (simulator.memory (Sum.inl cell)).2 = decide (cell = source.head) := by
    intro cell
    rw [representation.2 cell]
  unfold PhaseStack.compressSaved CompressedTape.compress
  rw [run_append, run_cons, run_nil, PhaseStack.save_memory]
  simp only [ite_true]
  rw [run_append, (rotate_control _ _ _).2,
    HeadMarker.detect_correct (8 * half) source.head simulator hhead hmarker]

theorem expansion_correct (half : ℕ) (slot originalHead : ℤ)
    (source : ObliviousPhase.Configuration State Symbol) (simulator : LeafStep.SimulatorConfiguration State Symbol)
    (representation : LeafStep.Represents source simulator)
    (choice : (simulator.memory (Sum.inr slot)).2 = decide (originalHead < 0)) :
    LeafStep.Represents (source.permute (compressionPermutation half originalHead).symm)
      (run (PhaseStack.expand half slot) simulator) := by
  unfold PhaseStack.expand
  rw [run_cons, PhaseStack.load_memory]
  have hshift : (if decide (originalHead < 0) then -(half : ℤ) else -(-(half : ℤ))) =
      -(compressionShift half originalHead) := by
    by_cases hnegative : originalHead < 0 <;> simp [compressionShift, hnegative]
  constructor
  · rw [(rotate_control _ _ _).1]
    exact representation.1
  · intro cell
    rw [rotate_main]
    dsimp only
    rw [choice, hshift, representation.2]
    simp only [compressionPermutation, TapeRotation.permutation_symm, ObliviousPhase.Configuration.permute]
    congr 1
    rw [← TapeRotation.permutation_symm (8 * half) (-compressionShift half originalHead)]
    simp only [Equiv.symm_apply_eq]

def instructions (machine : Machine State Symbol) (topLevel : ℕ) :
    ℕ → ℕ → List (StepInstruction State Symbol)
  | 0, _ => LeafStep.instructions machine
  | level + 1, nextSlot =>
      PhaseStack.compressSaved (2 ^ level) (PhaseStack.stackSlot topLevel nextSlot) ++
      instructions machine topLevel level (nextSlot + 1) ++
      PhaseStack.compressSaved (2 ^ level) (PhaseStack.stackSlot topLevel (nextSlot + 1)) ++
      instructions machine topLevel level (nextSlot + 2) ++
      PhaseStack.expand (2 ^ level) (PhaseStack.stackSlot topLevel (nextSlot + 1)) ++
      PhaseStack.expand (2 ^ level) (PhaseStack.stackSlot topLevel nextSlot)

theorem leaf_buffer (machine : Machine State Symbol) (simulator : LeafStep.SimulatorConfiguration State Symbol)
    (cell : ℤ) : (run (LeafStep.instructions machine) simulator).memory (Sum.inr cell) =
      simulator.memory (Sum.inr cell) := by
  unfold LeafStep.instructions
  rw [run_append, LeafStep.writeCells_buffer]
  simp only [readHeads, run_cons, execute_readHead, run_nil]

theorem compression_preserves_slot (half : ℕ) (saved other : ℤ)
    (simulator : LeafStep.SimulatorConfiguration State Symbol)
    (outside : ¬ TapeRotation.inside (8 * half) other) (different : other ≠ saved) :
    (run (PhaseStack.compressSaved half saved) simulator).memory (Sum.inr other) = simulator.memory (Sum.inr other) := by
  unfold PhaseStack.compressSaved
  rw [run_append, run_cons, run_nil, PhaseStack.save_memory]
  simp only [Sum.inr.injEq, different, if_false]
  exact PhaseStack.compress_preserves_slot half other simulator outside

theorem expansion_preserves_slot (half : ℕ) (saved other : ℤ)
    (simulator : LeafStep.SimulatorConfiguration State Symbol) (outside : ¬ TapeRotation.inside (8 * half) other) :
    (run (PhaseStack.expand half saved) simulator).memory (Sum.inr other) = simulator.memory (Sum.inr other) := by
  unfold PhaseStack.expand
  rw [run_cons, PhaseStack.load_memory, rotate_buffer_outside _ _ _ other outside]

/-- A phase never overwrites a choice saved by one of its callers. -/
theorem preserves_earlier_slot (machine : Machine State Symbol) (topLevel level nextSlot oldSlot : ℕ)
    (hlevel : level ≤ topLevel) (hold : oldSlot < nextSlot)
    (simulator : LeafStep.SimulatorConfiguration State Symbol) :
    (run (instructions machine topLevel level nextSlot) simulator).memory
        (Sum.inr (PhaseStack.stackSlot topLevel oldSlot)) =
      simulator.memory (Sum.inr (PhaseStack.stackSlot topLevel oldSlot)) := by
  induction level generalizing nextSlot simulator with
  | zero => exact leaf_buffer machine simulator _
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
      rw [expansion_preserves_slot _ _ _ _ hout, expansion_preserves_slot _ _ _ _ hout,
        ih (nextSlot + 2) (by omega) (by omega), compression_preserves_slot _ _ _ _ hout hdiff',
        ih (nextSlot + 1) (by omega) (by omega), compression_preserves_slot _ _ _ _ hout hdiff]

set_option maxHeartbeats 1600000 in
/-- The complete fixed-control instruction list realizes the recursive
semantic phase. The premises are only source-head bounds and actual tape
representation; no simulation or runtime certificate is supplied. -/
theorem phase_represents (machine : Machine State Symbol) (topLevel level nextSlot : ℕ)
    (hlevel : level ≤ topLevel) (source : ObliviousPhase.Configuration State Symbol)
    (simulator : LeafStep.SimulatorConfiguration State Symbol) (representation : LeafStep.Represents source simulator)
    (headBound : |source.head| ≤ (2 ^ level : ℕ)) :
    LeafStep.Represents (machine.phaseExecution level source)
      (run (instructions machine topLevel level nextSlot) simulator) := by
  induction level generalizing nextSlot source simulator with
  | zero => exact LeafStep.step_correct machine source simulator representation (by simpa using headBound)
  | succ level ih =>
      let half : ℕ := 2 ^ level
      let firstSlot := PhaseStack.stackSlot topLevel nextSlot
      let secondSlot := PhaseStack.stackSlot topLevel (nextSlot + 1)
      let firstPermutation := compressionPermutation half source.head
      let compressedSource := source.permute firstPermutation
      let firstSource := machine.phaseExecution level compressedSource
      let secondPermutation := compressionPermutation half firstSource.head
      let secondSource := machine.phaseExecution level (firstSource.permute secondPermutation)
      let firstCompression := run (PhaseStack.compressSaved half firstSlot) simulator
      let firstRun := run (instructions machine topLevel level (nextSlot + 1)) firstCompression
      let secondCompression := run (PhaseStack.compressSaved half secondSlot) firstRun
      let secondRun := run (instructions machine topLevel level (nextSlot + 2)) secondCompression
      let firstExpansion := run (PhaseStack.expand half secondSlot) secondRun
      have hfull : |source.head| ≤ 2 * (half : ℤ) := by simpa [half, pow_succ, mul_comm] using headBound
      have hcompressed : |compressedSource.head| ≤ (half : ℤ) := compressed_head_bound half source hfull
      have hfirstSource : firstSource = machine.run half compressedSource :=
        machine.phaseExecution_correct level compressedSource hcompressed
      have hfirstHead : |firstSource.head| ≤ 2 * (half : ℤ) := by
        rw [hfirstSource]
        have h := machine.head_bound_run compressedSource half
        omega
      have hsecondHead : |(firstSource.permute secondPermutation).head| ≤ (half : ℤ) :=
        compressed_head_bound half firstSource hfirstHead
      have hfirstCompression := compression_saved_correct half firstSlot source simulator representation hfull
      have hfirstRun : LeafStep.Represents firstSource firstRun :=
        ih (nextSlot + 1) (by omega) compressedSource firstCompression hfirstCompression hcompressed
      have hsecondCompression := compression_saved_correct half secondSlot firstSource firstRun hfirstRun hfirstHead
      have hsecondRun : LeafStep.Represents secondSource secondRun :=
        ih (nextSlot + 2) (by omega) (firstSource.permute secondPermutation)
          secondCompression hsecondCompression hsecondHead
      have hout := PhaseStack.stackSlot_outside topLevel level nextSlot (by omega)
      have hdiff : firstSlot ≠ secondSlot := by
        intro heq
        have h := PhaseStack.stackSlot_injective topLevel heq
        omega
      have hfirstChoice : (firstRun.memory (Sum.inr firstSlot)).2 = decide (source.head < 0) := by
        change ((run (instructions machine topLevel level (nextSlot + 1)) firstCompression).memory
          (Sum.inr (PhaseStack.stackSlot topLevel nextSlot))).2 = _
        rw [preserves_earlier_slot machine topLevel level (nextSlot + 1) nextSlot (by omega) (by omega)]
        exact compression_saved_choice half firstSlot source simulator representation hfull
      have hsecondChoice : (secondRun.memory (Sum.inr secondSlot)).2 = decide (firstSource.head < 0) := by
        change ((run (instructions machine topLevel level (nextSlot + 2)) secondCompression).memory
          (Sum.inr (PhaseStack.stackSlot topLevel (nextSlot + 1)))).2 = _
        rw [preserves_earlier_slot machine topLevel level (nextSlot + 2) (nextSlot + 1) (by omega) (by omega)]
        exact compression_saved_choice half secondSlot firstSource firstRun hfirstRun hfirstHead
      have hfirstChoiceAfter : (firstExpansion.memory (Sum.inr firstSlot)).2 = decide (source.head < 0) := by
        change ((run (PhaseStack.expand half secondSlot) secondRun).memory (Sum.inr firstSlot)).2 = _
        rw [expansion_preserves_slot half secondSlot firstSlot secondRun hout]
        change ((run (instructions machine topLevel level (nextSlot + 2)) secondCompression).memory
          (Sum.inr (PhaseStack.stackSlot topLevel nextSlot))).2 = _
        rw [preserves_earlier_slot machine topLevel level (nextSlot + 2) nextSlot (by omega) (by omega)]
        change ((run (PhaseStack.compressSaved half secondSlot) firstRun).memory (Sum.inr firstSlot)).2 = _
        rw [compression_preserves_slot half secondSlot firstSlot firstRun hout hdiff]
        exact hfirstChoice
      have hfirstExpansion := expansion_correct half secondSlot firstSource.head secondSource secondRun
        hsecondRun hsecondChoice
      have hfinal := expansion_correct half firstSlot source.head
        (secondSource.permute secondPermutation.symm) firstExpansion hfirstExpansion hfirstChoiceAfter
      simpa only [instructions, run_append, Machine.phaseExecution] using hfinal

/-- Exact source-step preservation for the assembled finite-control program. -/
theorem source_run_correct (machine : Machine State Symbol) (topLevel level nextSlot : ℕ)
    (hlevel : level ≤ topLevel) (source : ObliviousPhase.Configuration State Symbol)
    (simulator : LeafStep.SimulatorConfiguration State Symbol) (representation : LeafStep.Represents source simulator)
    (headBound : |source.head| ≤ (2 ^ level : ℕ)) :
    LeafStep.Represents (machine.run (2 ^ level) source)
      (run (instructions machine topLevel level nextSlot) simulator) := by
  rw [← machine.phaseExecution_correct level source headBound]
  exact phase_represents machine topLevel level nextSlot hlevel source simulator representation headBound

/-- Exact instruction accounting for the entire assembled program. -/
theorem instruction_count (machine : Machine State Symbol) (topLevel level nextSlot : ℕ) :
    (instructions machine topLevel level nextSlot).length + 32 = (208 * level + 40) * 2 ^ level := by
  induction level generalizing nextSlot with
  | zero => rfl
  | succ level ih =>
      simp only [instructions, List.length_append, PhaseStack.compressSaved_length, PhaseStack.expand_length]
      have hfirst := ih (nextSlot + 1)
      have hsecond := ih (nextSlot + 2)
      rw [pow_succ]
      nlinarith

theorem instruction_count_le (machine : Machine State Symbol) (topLevel level nextSlot : ℕ) :
    (instructions machine topLevel level nextSlot).length ≤ 248 * (level + 1) * 2 ^ level := by
  have h := instruction_count machine topLevel level nextSlot
  nlinarith

/-- A genuine near-linear *instruction/event* bound, obtained from the fully
assembled program rather than from a weight assigned to unexpanded commands. -/
theorem horizon_instruction_count (machine : Machine State Symbol) (steps nextSlot : ℕ) (hsteps : 1 ≤ steps) :
    (instructions machine (horizonLevel steps) (horizonLevel steps) nextSlot).length ≤
      992 * steps * (Nat.log 2 steps + 1) := by
  have hcount := instruction_count_le machine (horizonLevel steps) (horizonLevel steps) nextSlot
  have hpower := horizon_at_most_twice steps hsteps
  have hlevel : horizonLevel steps + 1 ≤ 2 * (Nat.log 2 steps + 1) := by unfold horizonLevel; omega
  calc
    _ ≤ 248 * (horizonLevel steps + 1) * 2 ^ horizonLevel steps := hcount
    _ ≤ (248 * (2 * (Nat.log 2 steps + 1))) * (2 * steps) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hlevel) hpower
    _ = _ := by ring

def sourceInitial (machine : Machine State Symbol) (tape : ℤ → Symbol) :
    ObliviousPhase.Configuration State Symbol := ⟨machine.initialState, 0, tape⟩

def initialControl (machine : Machine State Symbol) (blank : Symbol) :
    Control (Registers State Symbol) (HeadMarker.Cell Symbol) :=
  ⟨⟨machine.initialState, 0, blank, .stay⟩, false, (blank, false)⟩

def initialMemory (blank : Symbol) (tape : ℤ → Symbol) : Address → HeadMarker.Cell Symbol
  | .inl cell => (tape cell, decide (cell = 0))
  | .inr _ => (blank, false)

def program (machine : Machine State Symbol) (blank : Symbol) (level : ℕ) :
    Program (ℤ → Symbol) Address (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol) :=
  ObliviousCopy.program (instructions machine level level 0) (Sum.inl 0)
    (initialControl machine blank) (initialMemory blank)

/-- Initialization only copies the raw source tape, puts its head at zero,
and inserts the source's input-independent initial state. -/
theorem initial_represents (machine : Machine State Symbol) (blank : Symbol) (tape : ℤ → Symbol) :
    LeafStep.Represents (sourceInitial machine tape)
      (⟨initialControl machine blank, initialMemory blank tape⟩ : LeafStep.SimulatorConfiguration State Symbol) := by
  exact ⟨rfl, fun _ => rfl⟩

theorem program_correct (machine : Machine State Symbol) (blank : Symbol) (level : ℕ) (tape : ℤ → Symbol) :
    LeafStep.Represents (machine.run (2 ^ level) (sourceInitial machine tape))
      ((program machine blank level).configurationAt tape (instructions machine level level 0).length) := by
  rw [program, ObliviousCopy.program_complete]
  exact source_run_correct machine level level 0 le_rfl (sourceInitial machine tape)
    _ (initial_represents machine blank tape) (by simp [sourceInitial])

/-- Exact output preservation by the backend's two causal heads. This is
still a semantic attention/local-map compilation; its matrix realization is
a separate obligation, not assumed by this theorem. -/
theorem two_head_output (machine : Machine State Symbol) (blank : Symbol) (level : ℕ)
    (finish : State → Output) (tape : ℤ → Symbol) :
    letI : Inhabited (HeadMarker.Cell Symbol) := ⟨(blank, false)⟩
    letI : Inhabited (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) := ⟨initialControl machine blank⟩
    ((program machine blank level).compile (instructions machine level level 0).length
      (fun control => finish control.auxiliary.state)).run tape =
        finish (machine.run (2 ^ level) (sourceInitial machine tape)).state := by
  letI : Inhabited (HeadMarker.Cell Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) := ⟨initialControl machine blank⟩
  rw [ObliviousProgram.Program.compile_output]
  exact congrArg finish (program_correct machine blank level tape).1

theorem terminal_step_fixed (machine : Machine State Symbol)
    (configuration : ObliviousPhase.Configuration State Symbol)
    (terminal : ∀ symbol, machine.transition configuration.state symbol = (configuration.state, symbol, Direction.stay)) :
    machine.step configuration = configuration := by
  apply ObliviousPhase.Configuration.ext
  · simp [Machine.step, terminal]
  · simp [Machine.step, terminal, Direction.displacement]
  · simp [Machine.step, terminal, Function.update_eq_self]

theorem terminal_run_fixed (machine : Machine State Symbol)
    (configuration : ObliviousPhase.Configuration State Symbol)
    (terminal : ∀ symbol, machine.transition configuration.state symbol = (configuration.state, symbol, Direction.stay))
    (steps : ℕ) : machine.run steps configuration = configuration := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [Machine.run, ih, terminal_step_fixed machine configuration terminal]

/-- Halting source states stutter, so power-of-two padding does not change
the computation. This is a direct source transition condition, not an
imported complexity or simulation law. -/
theorem terminal_run_after (machine : Machine State Symbol)
    (configuration : ObliviousPhase.Configuration State Symbol) (finish later : ℕ) (hle : finish ≤ later)
    (terminal : ∀ symbol, machine.transition (machine.run finish configuration).state symbol =
      ((machine.run finish configuration).state, symbol, Direction.stay)) :
    machine.run later configuration = machine.run finish configuration := by
  have htime : later = finish + (later - finish) := by omega
  rw [htime, Machine.run_add]
  exact terminal_run_fixed machine _ terminal _

theorem padded_program_correct (machine : Machine State Symbol) (blank : Symbol) (steps : ℕ)
    (tape : ℤ → Symbol)
    (terminal : ∀ symbol, machine.transition (machine.run steps (sourceInitial machine tape)).state symbol =
      ((machine.run steps (sourceInitial machine tape)).state, symbol, Direction.stay)) :
    LeafStep.Represents (machine.run steps (sourceInitial machine tape))
      ((program machine blank (horizonLevel steps)).configurationAt tape
        (instructions machine (horizonLevel steps) (horizonLevel steps) 0).length) := by
  have h := program_correct machine blank (horizonLevel steps) tape
  rw [terminal_run_after machine _ steps _ (horizon_covers steps) terminal] at h
  exact h

/-- Standard raw Boolean input initialization: each in-range tape cell
contains just its own input bit, and every other cell is blank. -/
def bitTape (blank : Symbol) (bitSymbol : Bool → Symbol) (input : TransformerAC0.Bits n) (position : ℤ) : Symbol :=
  if hposition : 0 ≤ position ∧ position < (n : ℤ) then
    bitSymbol (input ⟨position.toNat, by have h := hposition.2; omega⟩)
  else blank

@[simp] theorem bitTape_at (blank : Symbol) (bitSymbol : Bool → Symbol)
    (input : TransformerAC0.Bits n) (position : Fin n) :
    bitTape blank bitSymbol input (position.val : ℤ) = bitSymbol (input position) := by
  have hposition : 0 ≤ (position.val : ℤ) ∧ (position.val : ℤ) < (n : ℤ) := by
    have h := position.isLt
    omega
  simp only [bitTape, dif_pos hposition, Int.toNat_natCast]

theorem bitTape_outside (blank : Symbol) (bitSymbol : Bool → Symbol)
    (input : TransformerAC0.Bits n) (position : ℤ) (outside : position < 0 ∨ (n : ℤ) ≤ position) :
    bitTape blank bitSymbol input position = blank := by
  apply dif_neg
  omega

def bitProgram (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (n level : ℕ) : Program (TransformerAC0.Bits n) Address
      (Control (Registers State Symbol) (HeadMarker.Cell Symbol)) (HeadMarker.Cell Symbol) :=
  ObliviousCopy.program (instructions machine level level 0) (Sum.inl 0)
    (initialControl machine blank) (fun input => initialMemory blank (bitTape blank bitSymbol input))

theorem bitProgram_correct (machine : Machine State Symbol) (blank : Symbol) (bitSymbol : Bool → Symbol)
    (level : ℕ) (input : TransformerAC0.Bits n) :
    LeafStep.Represents (machine.run (2 ^ level) (sourceInitial machine (bitTape blank bitSymbol input)))
      ((bitProgram machine blank bitSymbol n level).configurationAt input
        (instructions machine level level 0).length) := by
  rw [bitProgram, ObliviousCopy.program_complete]
  exact source_run_correct machine level level 0 le_rfl _ _
    (initial_represents machine blank _) (by simp [sourceInitial])

end EfficientPhase
