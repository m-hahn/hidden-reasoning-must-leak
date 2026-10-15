import MultitapeMatrix
import ScheduleMatrix
import ProtocolMatrix
import EncryptedObliviousMatrix

/-!
# Native output suffix for a whole finite source output word

Read each requested output cell from the simulator's actual final memory.
Read-only suffix instructions leave this memory unchanged. One shared
numerical model emits its separator and every output token, whose Boolean
label is the corresponding source output bit.
-/

noncomputable section
namespace MultitapeOutputMatrix
open TransformerAC0 ObliviousProgram ObliviousCopy ObliviousPhase MultitapeMatrix
variable {tapes : ℕ} {State Symbol : Type*} [Fintype State] [Fintype Symbol]
variable {extra : ℕ}

def instructions (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  MultitapeEfficientPhase.instructions machine anchor level level 0 ++ (List.ofFn cells).map (readout outputTape)

def program (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol) (level : ℕ)
    (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) :=
  ObliviousCopy.program (instructions machine anchor level outputTape cells) (anchor, Sum.inl 0)
    (MultitapeEfficientPhase.initialControl machine blank) (MultitapeEfficientPhase.initialMemory blank)

theorem read_memory (outputTape : Fin tapes) (cell : ℤ)
    (configuration : MultitapeLeaf.SimulatorConfiguration tapes State Symbol) :
    (execute (readout outputTape cell) configuration).memory = configuration.memory := by
  funext address
  simp only [execute, readout, Instruction.address, Instruction.nextSymbol]
  split_ifs with h
  · subst address; rfl
  · rfl

theorem reads_memory (outputTape : Fin tapes) (cells : List ℤ)
    (configuration : MultitapeLeaf.SimulatorConfiguration tapes State Symbol) :
    (run (cells.map (readout outputTape)) configuration).memory = configuration.memory := by
  induction cells generalizing configuration with
  | nil => rfl
  | cons cell cells ih =>
      rw [List.map_cons, run_cons, ih, read_memory]

theorem program_memory (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol)
    (index : Fin (extra + 1)) :
    ((program machine anchor blank level outputTape cells).configurationAt tape
      (eventSteps machine anchor level + index.val)).memory =
      (run (MultitapeEfficientPhase.instructions machine anchor level level 0)
        ⟨MultitapeEfficientPhase.initialControl machine blank, MultitapeEfficientPhase.initialMemory blank tape⟩).memory := by
  rw [program, ObliviousCopy.program_prefix]
  · unfold instructions eventSteps
    rw [List.take_append, run_append, ← List.map_take]
    exact reads_memory _ _ _
  · simp only [instructions, List.length_append, List.length_map, List.length_ofFn, eventSteps]
    have h := index.isLt
    omega

theorem output_instruction (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (index : Fin (extra + 1)) :
    (program machine anchor blank level outputTape cells).instruction (eventSteps machine anchor level + index.val) =
      readout outputTape (cells index) := by
  have hlt : eventSteps machine anchor level + index.val < (instructions machine anchor level outputTape cells).length := by
    simp only [instructions, List.length_append, List.length_map, List.length_ofFn, eventSteps]
    have h := index.isLt
    omega
  unfold program ObliviousCopy.program
  dsimp only
  rw [dif_pos hlt]
  unfold instructions
  rw [List.getElem_append_right (by simp only [eventSteps]; omega)]
  simp only [eventSteps, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_ofFn]

theorem output_cell_correct (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (index : Fin (extra + 1))
    (tape : Fin tapes → ℤ → Symbol) :
    ((program machine anchor blank level outputTape cells).configurationAt tape
      (eventSteps machine anchor level + index.val + 1)).control.auxiliary.scanned outputTape =
      (machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells index) := by
  rw [Program.configurationAt, output_instruction]
  simp only [execute, Instruction.nextControl, Instruction.address, readout, Function.update_self]
  change (((program machine anchor blank level outputTape cells).configurationAt tape
    (eventSteps machine anchor level + index.val)).memory (outputTape, Sum.inl (cells index))).1 = _
  rw [program_memory]
  rw [(MultitapeEfficientPhase.source_run_correct machine anchor level level 0 le_rfl
    (MultitapeEfficientPhase.sourceInitial machine tape) _ (MultitapeEfficientPhase.initial_represents machine blank tape)
    (by simp [MultitapeEfficientPhase.sourceInitial])).2]

def model (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (decode : Symbol → Bool) :=
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  ProtocolMatrix.model (EncryptedObliviousMatrix.schedule (program machine anchor blank level outputTape cells)
    (eventSteps machine anchor level + extra))
    (ObliviousMatrix.vocabulary_positive (Control := SimulatorControl tapes State Symbol) (Symbol := SimulatorSymbol Symbol))
    ObliviousMatrix.transition (ObliviousMatrix.label (fun control => decode (control.auxiliary.scanned outputTape)))
    (eventSteps machine anchor level) (by omega)

def inputEncoding (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (tape : Fin tapes → ℤ → Symbol) :=
  RoutedMatrix.promptInput (fun p => ProtocolMatrix.dataToken
    (ObliviousMatrix.prompt (program machine anchor blank level outputTape cells) (eventSteps machine anchor level + extra) tape p))

theorem generated_output (machine : MultitapeTuring.Machine tapes State Symbol) (anchor : Fin tapes) (blank : Symbol)
    (level : ℕ) (outputTape : Fin tapes) (cells : Fin (extra + 1) → ℤ) (decode : Symbol → Bool)
    (tape : Fin tapes → ℤ → Symbol) (index : Fin (extra + 1)) :
    (model machine anchor blank level outputTape cells decode).parameters.outputLabel
      ((model machine anchor blank level outputTape cells decode).generatedToken
        (inputEncoding machine anchor blank level outputTape cells tape)
        ⟨eventSteps machine anchor level + 1 + index.val, by have h := index.isLt; omega⟩) =
      decode ((machine.run (2 ^ level) (MultitapeEfficientPhase.sourceInitial machine tape)).tape outputTape (cells index)) := by
  letI : Inhabited (SimulatorSymbol Symbol) := ⟨(blank, false)⟩
  letI : Inhabited (SimulatorControl tapes State Symbol) := ⟨MultitapeEfficientPhase.initialControl machine blank⟩
  unfold model inputEncoding
  rw [ProtocolMatrix.generated_correct]
  have hnot : eventSteps machine anchor level + 1 + index.val ≠ eventSteps machine anchor level := by omega
  simp only [ProtocolMatrix.target, hnot, ↓reduceIte]
  rw [EncryptedObliviousMatrix.token_correct]
  change ProtocolMatrix.label (ObliviousMatrix.label (Symbol := SimulatorSymbol Symbol)
    (fun control : SimulatorControl tapes State Symbol => decode (control.auxiliary.scanned outputTape)))
    (ProtocolMatrix.dataToken (ObliviousMatrix.traceEncoding _)) = _
  simp only [ProtocolMatrix.label, ProtocolMatrix.dataToken, Fin.lastCases_castSucc, ObliviousMatrix.label,
    ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf, Program.traceToken_control]
  have ht : (ProtocolMatrix.oldTime (steps := eventSteps machine anchor level + extra)
      (eventSteps machine anchor level) (by omega)
      ⟨eventSteps machine anchor level + 1 + index.val, by have h := index.isLt; omega⟩).val =
      eventSteps machine anchor level + index.val := by
    simp only [ProtocolMatrix.oldTime, show ¬eventSteps machine anchor level + 1 + index.val ≤ eventSteps machine anchor level by omega, ↓reduceIte]
    omega
  rw [ht, output_cell_correct]

end MultitapeOutputMatrix
