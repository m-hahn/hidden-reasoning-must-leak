import ExactTasks
import TalComplete

/-! # Complete same-model theorem for the three elementary tasks

All clauses refer to the explicitly compiled exact-alphabet fold matrices.
The general assembly lemma needs only the elementary fold identity; the
three concrete instances discharge that identity locally.
-/
noncomputable section
namespace ExactFoldTheorem
open TransformerAC0 Encryption FiniteInformation
variable {Control Input Label : Type*} [Fintype Control] [Fintype Input] [DecidableEq Input]
variable [Inhabited Control] [Inhabited Input] [Fintype Label] [Nonempty Label] {vocabulary : ℕ}
variable (alphabet : ExactEncryptedAlphabet.Alphabet vocabulary (Fintype.card (Option Control)))
variable (initial : Control) (update : Control → Input → Control) (label : Fin vocabulary → Bool)
variable (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)

def OutputCorrect : Prop := ∀ n (input : Fin n → Input)
  (seed : Bits (EncryptedFold.seedLengths Control Input stretch n)) (output : Fin 2),
    (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).generatedToken
      (ExactFold.inputEncoding alphabet initial update input seed)
      ⟨EncryptedFold.payloadLength Control Input n + 1 + output.val, by
        change EncryptedFold.payloadLength Control Input n + 1 + output.val < EncryptedFold.payloadLength Control Input n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (alphabet.output (EncryptedFold.outputCode
        (if output = 0 then some ((List.ofFn input).foldl update initial) else none)))

def Resources : Prop :=
  (∃ heads precision : ℕ, ∀ n,
    (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).architecture.layers = 1 ∧
    (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).architecture.heads = heads ∧
    (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).parameters.scalarBits = precision) ∧
  (∃ C : ℕ, ∀ n, (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).architecture.contextLength ≤ C * (n + 1)) ∧
  (∃ D P : ℕ, ∀ n,
    (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).architecture.hiddenWidth ≤ D * (n + 1) ∧
    (ExactFold.privateModel alphabet initial update stretch hstretch generator label n).architecture.parameterCount ≤ P * (n + 1) ^ 2) ∧
  (∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∀ n,
    (EncryptedFold.seedLengths Control Input stretch n : ℝ) ≤ C * (n + 1 : ℝ) ^ alpha)

def Privacy : Prop := ∀ (codeWidth : ℕ) (encoding : Fin (vocabulary + 1) → Bits codeWidth)
  (monitor : PolynomialMonitorFamily (fun n => (EncryptedFold.payloadLength Control Input n + 1) * codeWidth)),
  ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
    (distribution : FiniteDistribution (Fin n → Input)) (predicate : (Fin n → Input) → Bool),
    predictionSuccess distribution
      (fun input seed => ExactEncryptedAlphabet.encodedTrace alphabet (EncryptedFold.originalSchedule initial update n) EncryptedFold.originalTransition
        ((EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Input) stretch hstretch generator).generator n)
        (EncryptedFold.sources n) (EncryptedFold.decode (Control := Control) (Alphabet := Input)) label encoding
        (EncryptedFold.plainPrompt initial update input) seed) (monitor.monitor n) predicate ≤
      distribution.bestConstantSuccess predicate + error n

def Information : Prop := ∀ n, 1 ≤ n →
  let G := (EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Input) stretch hstretch generator).generator n
  let M := ExactFoldTrace.model alphabet initial update G label (fun _ => false);
  -Real.logb 2 (Real.sqrt (Tal.tailBound M.fiberDepth M.fiberSize n)) - (EncryptedFold.seedLengths Control Input stretch n : ℝ) ≤
    (Distribution.uniform ((Fin n → Input) × Bits (EncryptedFold.seedLengths Control Input stretch n))).mutualInformation Prod.fst
      (ExactFoldTrace.trace alphabet initial update G label)

def LengthBound : Prop := ∀ n, 1 ≤ n →
  let G := (EncryptedFold.generatorPrefix (Control := Control) (Alphabet := Input) stretch hstretch generator).generator n
  let M := ExactFoldTrace.model alphabet initial update G label (fun _ => false);
  -Real.logb 2 (Real.sqrt (Tal.tailBound M.fiberDepth M.fiberSize n)) / Real.logb 2 (vocabulary + 1 : ℕ) ≤
    ExactFoldTrace.expectedLength alphabet initial update G label

def Complete : Prop :=
  OutputCorrect alphabet initial update label stretch hstretch generator ∧
  Resources alphabet initial update label stretch hstretch generator ∧
  Privacy alphabet initial update label stretch hstretch generator ∧
  Information alphabet initial update label stretch hstretch generator ∧
  LengthBound alphabet initial update label stretch hstretch generator

theorem complete_from_Tal (tal : Tal.FourierTailTheorem) (secure : generator.IsPseudorandom)
    (pairing : Input ≃ Bool × Label)
    (correct : ∀ {n} (input : Fin n → Input),
      label (alphabet.output (EncryptedFold.outputCode (some ((List.ofFn input).foldl update initial)))) =
        Tal.parity (fun i => (pairing (input i)).1)) :
    Complete alphabet initial update label stretch hstretch generator := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n input seed output
    exact ExactFold.generated_output _ _ _ _ _ _ _ _
  · refine ⟨?_, ?_, ExactFold.polynomial_resources alphabet initial update stretch hstretch generator label, ?_⟩
    · refine ⟨(ExactFold.privateModel alphabet initial update stretch hstretch generator label 0).architecture.heads,
        (ExactFold.privateModel alphabet initial update stretch hstretch generator label 0).parameters.scalarBits, ?_⟩
      intro n
      exact ⟨rfl, rfl, rfl⟩
    · exact ⟨_, ExactFold.context_linear alphabet initial update stretch hstretch generator label⟩
    · obtain ⟨c, _, _, hpos, hsub, hbound⟩ := EncryptedFold.seed_sublinear (Control := Control) (Alphabet := Input) stretch hstretch
      exact ⟨1 / c, _, hpos, hsub, hbound⟩
  · intro codeWidth encoding monitor
    exact ExactFold.no_readability alphabet initial update stretch hstretch generator secure label encoding monitor
  · intro n hn
    exact ExactFoldTrace.information_lower_bound _ _ _ _ _ tal pairing correct hn
  · intro n hn
    have hv : 1 < vocabulary + 1 := by have h := ExactEncryptedAlphabet.positive alphabet; omega
    exact ExactFoldTrace.expected_length_lower_bound _ _ _ _ _ tal pairing correct hn hv

theorem complete (secure : generator.IsPseudorandom)
    (pairing : Input ≃ Bool × Label)
    (correct : ∀ {n} (input : Fin n → Input),
      label (alphabet.output (EncryptedFold.outputCode (some ((List.ofFn input).foldl update initial)))) =
        Tal.parity (fun i => (pairing (input i)).1)) :
    Complete alphabet initial update label stretch hstretch generator :=
  complete_from_Tal alphabet initial update label stretch hstretch generator
    TalComplete.fourierTailTheorem secure pairing correct

end ExactFoldTheorem

namespace ExactTasks
open TransformerAC0 TaskReductions ElementaryTaskUpper ExactTaskAlphabet
local instance : Fintype S5 := groupEnumeration

/-- The only research premise is ordinary PRG security.
The full S₅ result, positive addition convention, exact vocabularies, native
EOS, linear upper bounds, seeded MI, and privacy all use the same models. -/
theorem elementary_tasks_complete
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
    (secure : generator.IsPseudorandom) :
    ExactFoldTheorem.Complete binaryAlphabet false Bool.xor binaryAlphabet.readBit stretch hstretch generator ∧
    ExactFoldTheorem.Complete groupAlphabet (1 : S5) (· * ·) groupReadBit stretch hstretch generator ∧
    ExactFoldTheorem.Complete additionAlphabet false additionUpdate additionAlphabet.readBit stretch hstretch generator :=
  ⟨ExactFoldTheorem.complete _ _ _ _ _ _ _ secure boolPairing parity_algebra,
    ExactFoldTheorem.complete _ _ _ _ _ _ _ secure s5Pairing s5_algebra,
    ExactFoldTheorem.complete _ _ _ _ _ _ _ secure positiveAdditionPairing100 addition_algebra⟩

end ExactTasks
