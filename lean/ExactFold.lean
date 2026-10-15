import ExactTaskAlphabet
import EncryptedFold

/-! # Actual linear encrypted folds in exact task alphabets -/

noncomputable section
namespace ExactFold
open TransformerAC0 Encryption
variable {Control Input : Type*} [Fintype Control] [Fintype Input] [Inhabited Control] [Inhabited Input]
variable {vocabulary n seedLength locality : ℕ}

def model (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (n : ℕ)
    (generator : LocalGenerator seedLength (EncryptedFold.payloadLength Control Input n + 1) locality)
    (label : Fin vocabulary → Bool) :=
  ExactEncryptedAlphabet.model alphabet (EncryptedFold.originalSchedule initial update n) EncryptedFold.originalTransition
    generator (EncryptedFold.sources n) (EncryptedFold.decode (Control := Control) (Alphabet := Input)) label

def inputEncoding (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (input : Fin n → Input) (seed : Bits seedLength) :=
  ExactEncryptedAlphabet.inputEncoding alphabet (EncryptedFold.plainPrompt initial update input) seed

theorem generated_output (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control)
    (generator : LocalGenerator seedLength (EncryptedFold.payloadLength Control Input n + 1) locality)
    (label : Fin vocabulary → Bool) (input : Fin n → Input) (seed : Bits seedLength) (output : Fin 2) :
    (model alphabet initial update n generator label).generatedToken (inputEncoding alphabet initial update input seed)
      ⟨EncryptedFold.payloadLength Control Input n + 1 + output.val, by
        change EncryptedFold.payloadLength Control Input n + 1 + output.val < EncryptedFold.payloadLength Control Input n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (alphabet.output (EncryptedFold.outputCode
        (if output = 0 then some ((List.ofFn input).foldl update initial) else none))) := by
  unfold model inputEncoding
  rw [ExactEncryptedAlphabet.generated_correct]
  change ExactEncryptedAlphabet.protocolErase alphabet
    ((EncryptedFold.model initial update n generator).generatedToken (EncryptedFold.inputEncoding initial update input seed) _) = _
  rw [EncryptedFold.generated_output, ExactEncryptedAlphabet.protocolErase_data, ExactEncryptedAlphabet.erase_result]

def privateModel (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (label : Fin vocabulary → Bool) (n : ℕ) :=
  model alphabet initial update n ((EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Input) stretch hstretch generator).generator n) label

theorem polynomial_resources (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (label : Fin vocabulary → Bool) :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (privateModel alphabet initial update stretch hstretch generator label n).architecture.hiddenWidth ≤ dimensionCoefficient * (n + 1) ∧
      (privateModel alphabet initial update stretch hstretch generator label n).architecture.parameterCount ≤ parameterCoefficient * (n + 1) ^ 2 := by
  let C := ⌈SeedBudget.coefficient 1 stretch (ObliviousMatrix.vocabulary Control Input + 1)⌉₊ +
    4 * ObliviousMatrix.vocabulary Control Input + 3
  have hc : ∀ n, (privateModel alphabet initial update stretch hstretch generator label n).architecture.contextLength + 1 ≤ C * (n + 1) := by
    intro n
    have h := EncryptedFold.context_linear initial update stretch hstretch generator n
    change (privateModel alphabet initial update stretch hstretch generator label n).architecture.contextLength ≤ _ at h
    dsimp [C]
    nlinarith
  simpa only [pow_one, Nat.mul_one] using ExactEncryptedAlphabet.polynomial_resources alphabet
    (EncryptedFold.originalSchedule initial update) EncryptedFold.originalTransition
    (EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Input) stretch hstretch generator)
    (fun n => EncryptedFold.sources n) (fun _ => EncryptedFold.decode (Control := Control) (Alphabet := Input)) label C 1
    (fun n => by simpa only [pow_one] using hc n)

theorem context_linear (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (label : Fin vocabulary → Bool) (n : ℕ) :
    (privateModel alphabet initial update stretch hstretch generator label n).architecture.contextLength ≤
      (⌈SeedBudget.coefficient 1 stretch (ObliviousMatrix.vocabulary Control Input + 1)⌉₊ +
        4 * ObliviousMatrix.vocabulary Control Input + 2) * (n + 1) :=
  EncryptedFold.context_linear initial update stretch hstretch generator n

theorem no_readability {codeWidth : ℕ} (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
    (initial : Control) (update : Control → Input → Control) (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) (label : Fin vocabulary → Bool)
    (encoding : Fin (vocabulary + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (EncryptedFold.payloadLength Control Input n + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Fin n → Input)) (predicate : (Fin n → Input) → Bool),
      predictionSuccess distribution
        (fun input seed => ExactEncryptedAlphabet.encodedTrace alphabet (EncryptedFold.originalSchedule initial update n) EncryptedFold.originalTransition
          ((EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Input) stretch hstretch generator).generator n)
          (EncryptedFold.sources n) (EncryptedFold.decode (Control := Control) (Alphabet := Input)) label encoding
          (EncryptedFold.plainPrompt initial update input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  ExactEncryptedAlphabet.no_readability_finite alphabet (EncryptedFold.originalSchedule initial update) EncryptedFold.originalTransition
    (EncryptedFold.generatorPrefix stretch hstretch generator) (EncryptedFold.generatorPrefix_secure stretch hstretch generator secure)
    (fun n => EncryptedFold.sources n) (fun _ => EncryptedFold.decode (Control := Control) (Alphabet := Input)) label
    (fun _ => EncryptedFold.plainPrompt initial update) encoding monitor (ObliviousMatrix.vocabulary Control Input) 1
    (fun _ => by unfold EncryptedFold.eventCount; simp [Nat.mul_comm])

end ExactFold
