import EncryptedFiniteReadout
import ElementaryTaskUpper
import SeedBudget
import PRGRestriction
import PRGReindex
import DelimitedWord
import PrivatePolynomialTime

/-!
# Linear encrypted task folds with a native complete result and EOS

Only the fixed finite transition sees the accumulator. The prompt contains
the raw input symbols and raw seed bits. Reasoning is generated as two
ciphertext tokens; after its separator the same matrices emit the complete
control value and then EOS.
-/

noncomputable section
namespace EncryptedFold
open TransformerAC0 Encryption RoutedSchedule
variable {Control Alphabet : Type*} [Fintype Control] [Fintype Alphabet]
variable [Inhabited Control] [Inhabited Alphabet] {n seedLength locality : ℕ}

def eventCount (n : ℕ) := n + 1
def payloadLength (Control Alphabet : Type*) [Fintype Control] [Fintype Alphabet] (n : ℕ) :=
  eventCount n * ObliviousMatrix.vocabulary Control Alphabet

def originalSchedule (initial : Control) (update : Control → Alphabet → Control) (n : ℕ) :=
  BinarySchedule.schedule (EncryptedObliviousMatrix.schedule (FoldProgram.program initial update n) (eventCount n))
    (ObliviousMatrix.vocabulary_positive (Control := Control) (Symbol := Alphabet))

def originalTransition :
    Fin (ObliviousMatrix.opcodes Control Alphabet * (ObliviousMatrix.vocabulary Control Alphabet + 1)) →
    (Fin (2 * ObliviousMatrix.vocabulary Control Alphabet) → Fin 2) → Fin 2 :=
  BinarySchedule.transition ObliviousMatrix.vocabulary_positive ObliviousMatrix.transition (fun _ => false)

def plainPrompt (initial : Control) (update : Control → Alphabet → Control) (input : Fin n → Alphabet) :=
  BinarySchedule.prompt (ObliviousMatrix.prompt (FoldProgram.program initial update n) (eventCount n) input)

def sources (n : ℕ) : Fin 2 → Fin (ObliviousMatrix.vocabulary Control Alphabet) → Fin (payloadLength Control Alphabet n) :=
  fun _ bit => finProdFinEquiv (Fin.last n, bit)

def outputCode : Option Control ≃ Fin (Fintype.card (Option Control)) := Fintype.equivFin _

def decode (output : Fin 2) (word : Bits (ObliviousMatrix.vocabulary Control Alphabet)) : Fin (Fintype.card (Option Control)) :=
  outputCode (if output = 0 then some (ObliviousMatrix.controlOf (ObliviousMatrix.tokenCode.symm
    (RoutedMatrix.decodeIndicator ObliviousMatrix.vocabulary_positive word))) else none)

def model (initial : Control) (update : Control → Alphabet → Control) (n : ℕ)
    (generator : LocalGenerator seedLength (payloadLength Control Alphabet n + 1) locality) :=
  EncryptedFiniteReadout.model (originalSchedule initial update n) originalTransition generator (sources n)
    (decode (Control := Control) (Alphabet := Alphabet))

def inputEncoding (initial : Control) (update : Control → Alphabet → Control) (input : Fin n → Alphabet) (seed : Bits seedLength) :=
  EncryptedFiniteReadout.inputEncoding (outputCard := Fintype.card (Option Control)) (plainPrompt initial update input) seed

theorem block_plain (initial : Control) (update : Control → Alphabet → Control) (input : Fin n → Alphabet) (output : Fin 2) :
    (fun bit => EncryptedBinaryMatrix.plainTranscript (originalSchedule initial update n) originalTransition
      (plainPrompt initial update input) (sources (Control := Control) (Alphabet := Alphabet) n output bit)) =
      RoutedMatrix.indicator (ObliviousMatrix.traceEncoding ((FoldProgram.program initial update n).traceToken input n)) := by
  funext bit
  unfold EncryptedBinaryMatrix.plainTranscript originalSchedule originalTransition plainPrompt
  rw [BinarySchedule.token_correct]
  have hnot : (sources (Control := Control) (Alphabet := Alphabet) n output bit).castSucc.val ≠
      eventCount n * ObliviousMatrix.vocabulary Control Alphabet :=
    Nat.ne_of_lt (sources (Control := Control) (Alphabet := Alphabet) n output bit).isLt
  simp only [BinarySchedule.target, hnot, ↓reduceIte, BinarySchedule.tokenBit_bitToken]
  have hevent : BinarySchedule.eventTime (ObliviousMatrix.vocabulary_positive (Control := Control) (Symbol := Alphabet))
      (sources (Control := Control) (Alphabet := Alphabet) n output bit).castSucc =
        ⟨n, by unfold eventCount; omega⟩ := by
    apply Fin.ext
    change (bit.val + ObliviousMatrix.vocabulary Control Alphabet * n) / ObliviousMatrix.vocabulary Control Alphabet = n
    simpa only [Nat.mul_comm, Nat.add_comm] using BinarySchedule.quotient_block ObliviousMatrix.vocabulary_positive n bit
  have hbit : BinarySchedule.codeBit (ObliviousMatrix.vocabulary_positive (Control := Control) (Symbol := Alphabet))
      (sources (Control := Control) (Alphabet := Alphabet) n output bit).castSucc = bit := by
    apply Fin.ext
    change (bit.val + ObliviousMatrix.vocabulary Control Alphabet * n) % ObliviousMatrix.vocabulary Control Alphabet = bit.val
    simpa only [Nat.mul_comm, Nat.add_comm] using BinarySchedule.remainder_block n bit
  rw [hevent, hbit, EncryptedObliviousMatrix.token_correct]

theorem generated_output (initial : Control) (update : Control → Alphabet → Control)
    (generator : LocalGenerator seedLength (payloadLength Control Alphabet n + 1) locality)
    (input : Fin n → Alphabet) (seed : Bits seedLength) (output : Fin 2) :
    (model initial update n generator).generatedToken (inputEncoding initial update input seed)
      ⟨payloadLength Control Alphabet n + 1 + output.val, by
        change payloadLength Control Alphabet n + 1 + output.val < payloadLength Control Alphabet n + 3
        have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (EncryptedFiniteReadout.result
        (outputCode (if output = 0 then some ((List.ofFn input).foldl update initial) else none))) := by
  unfold model inputEncoding
  unfold payloadLength
  rw [EncryptedFiniteReadout.output_correct, block_plain]
  unfold decode
  rw [RoutedMatrix.decodeIndicator_indicator]
  simp only [ObliviousMatrix.traceEncoding, Equiv.symm_apply_apply, ObliviousMatrix.controlOf,
    ObliviousProgram.Program.traceToken_control, FoldProgram.control_final]

theorem context_length (initial : Control) (update : Control → Alphabet → Control) (n : ℕ)
    (generator : LocalGenerator seedLength (payloadLength Control Alphabet n + 1) locality) :
    (model initial update n generator).architecture.contextLength =
      seedLength + (2 * n + 4) * ObliviousMatrix.vocabulary Control Alphabet + 2 := by
  rw [model, EncryptedFiniteReadout.context_length]
  change seedLength + (n + 3) * ObliviousMatrix.vocabulary Control Alphabet +
    ((n + 1) * ObliviousMatrix.vocabulary Control Alphabet) + 1 + 1 = _
  ring

def seedLengths (Control Alphabet : Type*) [Fintype Control] [Fintype Alphabet] (stretch : ℝ) : ℕ → ℕ :=
  SeedBudget.length 1 stretch (ObliviousMatrix.vocabulary Control Alphabet + 1)

theorem capacity (stretch : ℝ) (hstretch : 1 < stretch) (n : ℕ) :
    payloadLength Control Alphabet n + 1 ≤ ⌊(seedLengths Control Alphabet stretch n : ℝ) ^ stretch⌋₊ := by
  apply SeedBudget.stretch_floor_capacity (k := 1)
    (size := (ObliviousMatrix.vocabulary Control Alphabet + 1 : ℝ)) (by norm_num) hstretch (by positivity)
  have hn : (n + 1 : ℝ) ≤ (n + 1 : ℝ) * (Nat.log 2 (n + 1) + 1) := by
    nlinarith [(Nat.cast_nonneg (Nat.log 2 (n + 1)) : (0 : ℝ) ≤ Nat.log 2 (n + 1))]
  simp only [Real.rpow_one]
  unfold payloadLength eventCount
  push_cast
  nlinarith

def generatorPrefix (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) :
    NC0GeneratorFamily (seedLengths Control Alphabet stretch) (fun n => payloadLength Control Alphabet n + 1) :=
  PRGRestriction.family (PRGReindex.family generator (seedLengths Control Alphabet stretch)) (capacity stretch hstretch)

theorem generatorPrefix_secure (stretch : ℝ) (hstretch : 1 < stretch)
    (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (secure : generator.IsPseudorandom) :
    (generatorPrefix (Control := Control) (Alphabet := Alphabet) stretch hstretch generator).IsPseudorandom := by
  apply PRGRestriction.secure
  obtain ⟨degree, _, hinverse⟩ := SeedBudget.seed_inverse_bound (k := 1)
    (size := (ObliviousMatrix.vocabulary Control Alphabet + 1 : ℝ)) (by norm_num) hstretch
  apply PRGReindex.secure generator secure _ degree
  intro n
  exact (hinverse n).trans (Nat.pow_le_pow_left (Nat.le_succ _) degree)

def privateModel (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :=
  model initial update n ((generatorPrefix (Control := Control) (Alphabet := Alphabet) stretch hstretch generator).generator n)

theorem context_linear (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch) (n : ℕ) :
    (privateModel initial update stretch hstretch generator n).architecture.contextLength ≤
      (⌈SeedBudget.coefficient 1 stretch (ObliviousMatrix.vocabulary Control Alphabet + 1)⌉₊ +
        4 * ObliviousMatrix.vocabulary Control Alphabet + 2) * (n + 1) := by
  rw [privateModel, context_length]
  have hseed := SeedBudget.seed_polynomial_bound (k := 1)
    (size := (ObliviousMatrix.vocabulary Control Alphabet + 1 : ℝ)) (by norm_num) hstretch n
  change seedLengths Control Alphabet stretch n ≤ _ at hseed
  nlinarith

theorem seed_sublinear (stretch : ℝ) (hstretch : 1 < stretch) :
    ∃ c : ℝ, 1 < c ∧ c < stretch ∧ 0 < 1 / c ∧ 1 / c < 1 ∧ ∀ n : ℕ,
      (seedLengths Control Alphabet stretch n : ℝ) ≤
        (SeedBudget.coefficient 1 stretch (ObliviousMatrix.vocabulary Control Alphabet + 1) + 1) * (n + 1 : ℝ) ^ (1 / c) := by
  obtain ⟨c, hlo, hhi, hpos, hsub, hbound, _⟩ := SeedBudget.sublinear_seed_and_capacity
    (k := 1) (size := (ObliviousMatrix.vocabulary Control Alphabet + 1 : ℝ)) (by norm_num) hstretch (by positivity)
  exact ⟨c, hlo, hhi, hpos, hsub, hbound⟩

theorem no_readability {codeWidth : ℕ} (initial : Control) (update : Control → Alphabet → Control)
    (stretch : ℝ) (hstretch : 1 < stretch) (generator : PrivatePolynomialTime.SeedIndexedGenerator stretch)
    (secure : generator.IsPseudorandom)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + Fintype.card (Option Control) + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (payloadLength Control Alphabet n + 1) * codeWidth)) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Fin n → Alphabet)) (predicate : (Fin n → Alphabet) → Bool),
      predictionSuccess distribution
        (fun input seed => EncryptedFiniteReadout.encodedTrace (originalSchedule initial update n) originalTransition
          ((generatorPrefix (Control := Control) (Alphabet := Alphabet) stretch hstretch generator).generator n)
          (sources n) (decode (Control := Control) (Alphabet := Alphabet)) encoding (plainPrompt initial update input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n :=
  EncryptedFiniteReadout.no_readability_finite (originalSchedule initial update) originalTransition
    (fun n => sources n) (fun _ => decode (Control := Control) (Alphabet := Alphabet))
    (fun _ => plainPrompt initial update)
    (generatorPrefix stretch hstretch generator) (generatorPrefix_secure stretch hstretch generator secure)
    encoding monitor (ObliviousMatrix.vocabulary Control Alphabet) 1 (fun _ => by unfold eventCount; simp [Nat.mul_comm])

end EncryptedFold
