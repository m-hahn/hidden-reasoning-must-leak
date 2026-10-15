import CausalToken
import ProtocolEncryptedBinary
import SeededToken

/-!
# The same native encrypted protocol in the information lower bounds

Raw private seed wires are fixed in the lower-bound argument; no matrix
weights change. The first-separator transcript of the constructed numerical
model is therefore covered by the checked seeded footprint theorems.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace ProtocolToken
open TransformerAC0 Encryption
variable {n front steps heads opcodes seedLength locality : ℕ}

def rawInput (word : Bits (n + seedLength)) : Bits n := fun wire => word (Fin.castAdd seedLength wire)
def rawSeed (word : Bits (n + seedLength)) : Bits seedLength := fun wire => word (Fin.natAdd n wire)

theorem append_raw (word : Bits (n + seedLength)) : Fin.append (rawInput word) (rawSeed word) = word := by
  funext wire
  refine Fin.addCases (fun i => ?_) (fun i => ?_) wire <;> simp [rawInput, rawSeed]

variable (schedule : RoutedSchedule.Schedule front steps heads opcodes)
variable (transition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) (label : Fin 2 → Bool)
variable (generator : LocalGenerator seedLength (steps + 1) locality)
variable (plain : Bits n → Fin front → Fin 2)
variable (literal : Fin (front * 2) → Autoregressive.ContextLiteral n)
variable (literal_correct : ∀ input wire, (literal wire).eval input = RoutedMatrix.promptInput (plain input) wire)

include literal_correct

theorem prompt_append (input : Bits n) (seed : Bits seedLength) :
    CausalToken.promptInput (ProtocolEncryptedBinary.inputLiteral literal seedLength) (Fin.append input seed) =
      ProtocolEncryptedBinary.inputEncoding (plain input) seed := by
  funext wire
  exact ProtocolEncryptedBinary.inputLiteral_correct literal input (plain input) seed (literal_correct input) wire

theorem prompt_raw (word : Bits (n + seedLength)) :
    CausalToken.promptInput (ProtocolEncryptedBinary.inputLiteral literal seedLength) word =
      ProtocolEncryptedBinary.inputEncoding (plain (rawInput word)) (rawSeed word) := by
  have h := prompt_append plain literal literal_correct (rawInput word) (rawSeed word)
  rw [append_raw] at h
  exact h

theorem stops (word : Bits (n + seedLength)) :
    (ProtocolEncryptedBinary.model schedule transition label generator).generatedToken
      (CausalToken.promptInput (ProtocolEncryptedBinary.inputLiteral literal seedLength) word)
      ⟨steps, by omega⟩ = ProtocolMatrix.separator (EncryptedMatrix.packetCount 2) := by
  rw [prompt_raw plain literal literal_correct]
  exact ProtocolEncryptedBinary.separator_generated schedule transition label generator _ _

theorem before (word : Bits (n + seedLength)) (time : Fin steps) :
    (ProtocolEncryptedBinary.model schedule transition label generator).generatedToken
      (CausalToken.promptInput (ProtocolEncryptedBinary.inputLiteral literal seedLength) word)
      ⟨time.val, by have h := time.isLt; omega⟩ ≠ ProtocolMatrix.separator (EncryptedMatrix.packetCount 2) := by
  rw [prompt_raw plain literal literal_correct, ProtocolEncryptedBinary.payload_correct]
  exact ProtocolMatrix.data_ne_separator _

def tokenGenerator : TokenAutoregressive.Generator (n + seedLength) steps :=
  CausalToken.fixedGenerator (ProtocolEncryptedBinary.model schedule transition label generator)
    (ProtocolEncryptedBinary.inputLiteral literal seedLength) (ProtocolMatrix.separator (EncryptedMatrix.packetCount 2))
    (stops schedule transition label generator plain literal literal_correct)

theorem length_fixed (word : Bits (n + seedLength)) :
    (tokenGenerator schedule transition label generator plain literal literal_correct).length word = Fin.last steps :=
  CausalToken.fixed_length _ _ _ _ (before schedule transition label generator plain literal literal_correct) word

theorem answer_correct (input : Bits n) (seed : Bits seedLength) :
    (tokenGenerator schedule transition label generator plain literal literal_correct).answer (Fin.append input seed) =
      label (RoutedSchedule.token schedule transition (plain input) (Fin.last steps)) := by
  have h := CausalToken.fixed_answer _ _ _
    (stops schedule transition label generator plain literal literal_correct)
    (before schedule transition label generator plain literal literal_correct) (Fin.append input seed)
  rw [prompt_append plain literal literal_correct] at h
  exact h.trans (ProtocolEncryptedBinary.output_correct schedule transition label generator _ _)

/-- Leakage of the very same native matrix protocol used in the privacy
theorem. The only research premise for this lower bound is Tal's theorem. -/
theorem parity_leakage (tal : Tal.FourierTailTheorem)
    (correct : ∀ input, label (RoutedSchedule.token schedule transition (plain input) (Fin.last steps)) = Tal.parity input)
    (hn : 1 ≤ n) :
    let model := tokenGenerator schedule transition label generator plain literal literal_correct;
    -Real.logb 2 (Real.sqrt (Tal.tailBound model.fiberDepth model.fiberSize n)) - (seedLength : ℝ) ≤
      (FiniteInformation.Distribution.uniform (Bits n × Bits seedLength)).mutualInformation Prod.fst model.seededTrace := by
  apply TokenAutoregressive.Generator.seeded_footprint tal _ _ hn
  intro input seed
  rw [answer_correct]
  exact correct input

end ProtocolToken
