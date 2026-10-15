import ScheduleRecoding
import EncryptedFiniteReadout

/-!
# Native encrypted computation in the task's own vocabulary

Seed, plaintext, and ciphertext bits share two actual vocabulary symbols.
Public source positions, encoded as finite opcodes, recover their roles.
Output values share the task alphabet as well. Only the separator is added
by the protocol constructor; no packet-role tokens survive in the model.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace ExactEncryptedAlphabet
open TransformerAC0 Encryption RoutedSchedule
variable {front steps extra heads opcodes width outputCard vocabulary seedLength locality : ℕ}

structure Alphabet (vocabulary outputCard : ℕ) where
  bit : Bool → Fin vocabulary
  readBit : Fin vocabulary → Bool
  readBit_bit : ∀ value, readBit (bit value) = value
  output : Fin outputCard → Fin vocabulary

theorem positive (alphabet : Alphabet vocabulary outputCard) : 0 < vocabulary :=
  Nat.zero_lt_of_lt (alphabet.bit false).isLt

def erase (alphabet : Alphabet vocabulary outputCard) :
    Fin (EncryptedMatrix.packetCount 2 + outputCard) → Fin vocabulary :=
  Fin.addCases (fun packet => match EncryptedMatrix.packetCode.symm packet with
    | .inl token => alphabet.bit (BinarySchedule.tokenBit token)
    | .inr (.inl bit) => alphabet.bit bit
    | .inr (.inr (.inl word)) => alphabet.bit (word 1)
    | .inr (.inr (.inr bit)) => alphabet.bit bit) alphabet.output

@[simp] theorem erase_seed (alphabet : Alphabet vocabulary outputCard) (bit : Bool) :
    erase alphabet (EncryptedFiniteReadout.packet (EncryptedMatrix.seedPacket 2 bit)) = alphabet.bit bit := by
  simp [erase, EncryptedFiniteReadout.packet, EncryptedMatrix.seedPacket]

@[simp] theorem erase_plain (alphabet : Alphabet vocabulary outputCard) (token : Fin 2) :
    erase alphabet (EncryptedFiniteReadout.packet (EncryptedMatrix.plainPacket token)) = alphabet.bit (BinarySchedule.tokenBit token) := by
  simp [erase, EncryptedFiniteReadout.packet, EncryptedMatrix.plainPacket]

@[simp] theorem erase_cipher (alphabet : Alphabet vocabulary outputCard) (bit : Bool) :
    erase alphabet (EncryptedFiniteReadout.packet (EncryptedBinaryMatrix.binaryPacket bit)) = alphabet.bit bit := by
  cases bit <;> simp [erase, EncryptedFiniteReadout.packet, EncryptedBinaryMatrix.binaryPacket,
    EncryptedMatrix.cipherPacket, RoutedMatrix.indicator, BinarySchedule.bitToken]

@[simp] theorem erase_result (alphabet : Alphabet vocabulary outputCard) (value : Fin outputCard) :
    erase alphabet (EncryptedFiniteReadout.result value) = alphabet.output value := by
  simp [erase, EncryptedFiniteReadout.result]

def recover (alphabet : Alphabet vocabulary outputCard) (position : ℕ) (value : Fin vocabulary) :
    Fin (EncryptedMatrix.packetCount 2 + outputCard) :=
  EncryptedFiniteReadout.packet (if position < seedLength then EncryptedMatrix.seedPacket 2 (alphabet.readBit value)
    else if position < seedLength + front then EncryptedMatrix.plainPacket (BinarySchedule.bitToken (alphabet.readBit value))
    else EncryptedBinaryMatrix.binaryPacket (alphabet.readBit value))

theorem recover_seed (alphabet : Alphabet vocabulary outputCard) (position : ℕ) (before : position < seedLength) (bit : Bool) :
    recover (front := front) (seedLength := seedLength) alphabet position
      (erase alphabet (EncryptedFiniteReadout.packet (EncryptedMatrix.seedPacket 2 bit))) =
      EncryptedFiniteReadout.packet (EncryptedMatrix.seedPacket 2 bit) := by
  simp [recover, before, alphabet.readBit_bit]

theorem recover_plain (alphabet : Alphabet vocabulary outputCard) (position : ℕ)
    (after : seedLength ≤ position) (before : position < seedLength + front) (token : Fin 2) :
    recover (front := front) (seedLength := seedLength) alphabet position
      (erase alphabet (EncryptedFiniteReadout.packet (EncryptedMatrix.plainPacket token))) =
      EncryptedFiniteReadout.packet (EncryptedMatrix.plainPacket token) := by
  simp [recover, show ¬position < seedLength by omega, before, alphabet.readBit_bit]

theorem recover_cipher (alphabet : Alphabet vocabulary outputCard) (position : ℕ)
    (after : seedLength + front ≤ position) (bit : Bool) :
    recover (front := front) (seedLength := seedLength) alphabet position
      (erase alphabet (EncryptedFiniteReadout.packet (EncryptedBinaryMatrix.binaryPacket bit))) =
      EncryptedFiniteReadout.packet (EncryptedBinaryMatrix.binaryPacket bit) := by
  simp [recover, show ¬position < seedLength by omega, show ¬position < seedLength + front by omega,
    alphabet.readBit_bit]

def oldSchedule (original : Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :=
  EncryptedFiniteReadout.schedule original generator sources decode

def recovery (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :=
  fun time head => recover (front := front) (seedLength := seedLength) alphabet
    ((oldSchedule original generator sources decode).source time head).val

def schedule (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :=
  ScheduleRecoding.schedule (oldSchedule original generator sources decode) (recovery alphabet original generator sources decode)

def run (alphabet : Alphabet vocabulary outputCard)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2) :=
  ScheduleRecoding.transition (erase alphabet)
    (EncryptedFiniteReadout.run (outputCard := outputCard) (width := width) (locality := locality) originalTransition)

theorem old_payload (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin steps) :
    token (oldSchedule original generator sources decode) (EncryptedFiniteReadout.run originalTransition)
      (EncryptedFiniteReadout.prompt plain seed) (ReadoutSchedule.extendTime time) =
      EncryptedFiniteReadout.packet (EncryptedBinaryMatrix.binaryPacket
        (xor (EncryptedBinaryMatrix.plainTranscript original originalTransition plain time) (generator.generate seed time.castSucc))) := by
  unfold oldSchedule EncryptedFiniteReadout.schedule EncryptedFiniteReadout.run
  rw [ReadoutSchedule.prefix_correct]
  unfold EncryptedFiniteReadout.prompt
  rw [token_lift _ _ _ EncryptedFiniteReadout.project_packet, EncryptedReadout.base_payload]

theorem source_recovery (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength)
    (time : Fin (steps + extra + 1)) (head) :
    recovery alphabet original generator sources decode time head
      (erase alphabet (word (EncryptedFiniteReadout.prompt plain seed) time.val
        (fun previous => token (oldSchedule original generator sources decode) (EncryptedFiniteReadout.run originalTransition)
          (EncryptedFiniteReadout.prompt plain seed) ⟨previous.val, previous.isLt.trans time.isLt⟩)
        ((oldSchedule original generator sources decode).source time head))) =
      word (EncryptedFiniteReadout.prompt plain seed) time.val
        (fun previous => token (oldSchedule original generator sources decode) (EncryptedFiniteReadout.run originalTransition)
          (EncryptedFiniteReadout.prompt plain seed) ⟨previous.val, previous.isLt.trans time.isLt⟩)
        ((oldSchedule original generator sources decode).source time head) := by
  let source := (oldSchedule original generator sources decode).source time head
  have hsource : source.val < seedLength + front + steps :=
    ReadoutSchedule.source_before_readouts _ _ _ _
  change recover (front := front) (seedLength := seedLength) alphabet source.val
    (erase alphabet (word _ time.val _ source)) = word _ time.val _ source
  revert hsource
  refine Fin.addCases (fun position hsource => ?_) (fun previous hsource => ?_) source
  · simp only [word, Fin.addCases_left, EncryptedFiniteReadout.prompt]
    refine Fin.addCases (fun position => ?_) (fun position => ?_) position
    · simp only [EncryptedMatrix.prompt, Fin.addCases_left]
      exact recover_seed alphabet _ position.isLt _
    · simp only [EncryptedMatrix.prompt, Fin.addCases_right]
      apply recover_plain alphabet
      · change seedLength ≤ seedLength + position.val; omega
      · change seedLength + position.val < seedLength + front
        exact Nat.add_lt_add_left position.isLt _
  · simp only [word, Fin.addCases_right]
    have hprevious : previous.val < steps := by
      have hs := hsource
      change seedLength + front + previous.val < seedLength + front + steps at hs
      omega
    have htime : (⟨previous.val, previous.isLt.trans time.isLt⟩ : Fin (steps + extra + 1)) =
        ReadoutSchedule.extendTime (extra := extra) ⟨previous.val, hprevious⟩ := rfl
    rw [htime, old_payload]
    apply recover_cipher alphabet
    change seedLength + front ≤ seedLength + front + previous.val
    omega

def model (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) :=
  ProtocolMatrix.model (schedule alphabet original generator sources decode) (positive alphabet)
    (run alphabet originalTransition) label steps (by omega)

def inputEncoding (alphabet : Alphabet vocabulary outputCard) (plain : Fin front → Fin 2) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (fun p => ProtocolMatrix.dataToken (erase alphabet (EncryptedFiniteReadout.prompt plain seed p)))

theorem token_correct (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin (steps + extra + 1)) :
    token (schedule alphabet original generator sources decode) (run alphabet originalTransition)
      (fun p => erase alphabet (EncryptedFiniteReadout.prompt plain seed p)) time =
      erase alphabet (token (oldSchedule original generator sources decode) (EncryptedFiniteReadout.run originalTransition)
        (EncryptedFiniteReadout.prompt plain seed) time) :=
  ScheduleRecoding.token_correct _ _ _ _ _
    (source_recovery alphabet original originalTransition generator sources decode plain seed) time

def protocolErase (alphabet : Alphabet vocabulary outputCard) :
    Fin (EncryptedMatrix.packetCount 2 + outputCard + 1) → Fin (vocabulary + 1) :=
  Fin.lastCases (ProtocolMatrix.separator vocabulary) (fun value => ProtocolMatrix.dataToken (erase alphabet value))

@[simp] theorem protocolErase_data (alphabet : Alphabet vocabulary outputCard)
    (value : Fin (EncryptedMatrix.packetCount 2 + outputCard)) :
    protocolErase alphabet (ProtocolMatrix.dataToken value) = ProtocolMatrix.dataToken (erase alphabet value) := by
  simp [protocolErase, ProtocolMatrix.dataToken]

theorem generated_correct (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin (steps + extra + 2)) :
    (model alphabet original originalTransition generator sources decode label).generatedToken (inputEncoding alphabet plain seed) time =
      protocolErase alphabet ((EncryptedFiniteReadout.model original originalTransition generator sources decode).generatedToken
        (EncryptedFiniteReadout.inputEncoding plain seed) time) := by
  rw [model, inputEncoding, ProtocolMatrix.generated_correct]
  rw [EncryptedFiniteReadout.model, EncryptedFiniteReadout.inputEncoding, ProtocolMatrix.generated_correct]
  by_cases hsep : time.val = steps
  · simp [ProtocolMatrix.target, hsep, protocolErase, ProtocolMatrix.separator]
  · simp only [ProtocolMatrix.target, hsep, ↓reduceIte, protocolErase_data]
    exact congrArg ProtocolMatrix.dataToken (token_correct alphabet original originalTransition generator sources decode plain seed _)

theorem payload_correct (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin steps) :
    (model alphabet original originalTransition generator sources decode label).generatedToken (inputEncoding alphabet plain seed)
      ⟨time.val, by have h := time.isLt; omega⟩ =
      ProtocolMatrix.dataToken (alphabet.bit (xor (EncryptedBinaryMatrix.plainTranscript original originalTransition plain time)
        (generator.generate seed time.castSucc))) := by
  rw [generated_correct, EncryptedFiniteReadout.payload_correct, protocolErase_data, erase_cipher]

theorem output_correct (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) (plain : Fin front → Fin 2) (seed : Bits seedLength) (output : Fin (extra + 1)) :
    (model alphabet original originalTransition generator sources decode label).generatedToken (inputEncoding alphabet plain seed)
      ⟨steps + 1 + output.val, by have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (alphabet.output (decode output (fun bit =>
        EncryptedBinaryMatrix.plainTranscript original originalTransition plain (sources output bit)))) := by
  rw [generated_correct, EncryptedFiniteReadout.output_correct, protocolErase_data, erase_result]

theorem separator_generated (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    (model alphabet original originalTransition generator sources decode label).generatedToken (inputEncoding alphabet plain seed)
      ⟨steps, by omega⟩ = ProtocolMatrix.separator vocabulary :=
  ProtocolMatrix.separator_generated _ _ _ _ _ _ _

def encodedTrace {codeWidth : ℕ} (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) (encoding : Fin (vocabulary + 1) → Bits codeWidth)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) : Bits ((steps + 1) * codeWidth) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  encoding ((model alphabet original originalTransition generator sources decode label).generatedToken
    (inputEncoding alphabet plain seed) (Fin.castLE (by omega) pair.1)) pair.2

theorem encodedTrace_eq_original {codeWidth : ℕ} (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) (encoding : Fin (vocabulary + 1) → Bits codeWidth)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    encodedTrace alphabet original originalTransition generator sources decode label encoding plain seed =
      EncryptedFiniteReadout.encodedTrace original originalTransition generator sources decode
        (fun value => encoding (protocolErase alphabet value)) plain seed := by
  funext wire
  simp only [encodedTrace, EncryptedFiniteReadout.encodedTrace, generated_correct]

theorem no_readability_finite {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)]
    {fronts times extras seedLengths : ℕ → ℕ} {codeWidth : ℕ}
    (alphabet : Alphabet vocabulary outputCard) (originals : ∀ n, Schedule (fronts n) (times n) heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1)) (secure : generator.IsPseudorandom)
    (sources : ∀ n, Fin (extras n + 1) → Fin width → Fin (times n))
    (decode : ∀ n, Fin (extras n + 1) → Bits width → Fin outputCard) (label : Fin vocabulary → Bool)
    (prompts : ∀ n, Input n → Fin (fronts n) → Fin 2)
    (encoding : Fin (vocabulary + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (bounded : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
      predictionSuccess distribution
        (fun input seed => encodedTrace alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n)
          label encoding (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  simp_rw [encodedTrace_eq_original]
  exact EncryptedFiniteReadout.no_readability_finite originals originalTransition sources decode prompts generator secure
    (fun value => encoding (protocolErase alphabet value)) monitor coefficient exponent bounded

theorem bit_injective (alphabet : Alphabet vocabulary outputCard) : Function.Injective alphabet.bit := by
  intro first second heq
  simpa only [alphabet.readBit_bit] using congrArg alphabet.readBit heq

theorem inputEncoding_eq (alphabet : Alphabet vocabulary outputCard) (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    inputEncoding alphabet plain seed = RoutedMatrix.promptInput
      (Fin.addCases (fun index => ProtocolMatrix.dataToken (alphabet.bit (seed index)))
        (fun index => ProtocolMatrix.dataToken (alphabet.bit (BinarySchedule.tokenBit (plain index))))) := by
  funext wire
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.addCases (fun position => ?_) (fun position => ?_) position <;>
    simp [EncryptedFiniteReadout.prompt, EncryptedMatrix.prompt]

def mappedLiteral {n : ℕ} (alphabet : Alphabet vocabulary outputCard)
    (literal : Fin 2 → Autoregressive.ContextLiteral n) (token : Fin (vocabulary + 1)) : Autoregressive.ContextLiteral n :=
  if token = ProtocolMatrix.dataToken (alphabet.bit false) then literal 0
  else if token = ProtocolMatrix.dataToken (alphabet.bit true) then literal 1
  else .constant false

theorem mappedLiteral_correct {n : ℕ} (alphabet : Alphabet vocabulary outputCard)
    (literal : Fin 2 → Autoregressive.ContextLiteral n) (input : Bits n) (plain : Fin 2)
    (correct : ∀ token, (literal token).eval input = decide (token = plain)) (token : Fin (vocabulary + 1)) :
    (mappedLiteral alphabet literal token).eval input =
      decide (token = ProtocolMatrix.dataToken (alphabet.bit (BinarySchedule.tokenBit plain))) := by
  have hne : ProtocolMatrix.dataToken (alphabet.bit false) ≠ ProtocolMatrix.dataToken (alphabet.bit true) := by
    intro heq
    have hb := bit_injective alphabet (Fin.castSucc_injective _ heq)
    cases hb
  fin_cases plain <;>
    by_cases hfalse : token = ProtocolMatrix.dataToken (alphabet.bit false) <;>
    by_cases htrue : token = ProtocolMatrix.dataToken (alphabet.bit true)
  all_goals simp [mappedLiteral, hfalse, htrue, correct, BinarySchedule.tokenBit]
  all_goals simp_all [Autoregressive.ContextLiteral.eval]

def inputLiteral {n : ℕ} (alphabet : Alphabet vocabulary outputCard)
    (literal : Fin (front * 2) → Autoregressive.ContextLiteral n) (seedLength : ℕ) :
    Fin ((seedLength + front) * (vocabulary + 1)) → Autoregressive.ContextLiteral (n + seedLength) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  Fin.addCases
    (fun index => EfficientMatrix.bitLiteral
      (decide (pair.2 = ProtocolMatrix.dataToken (alphabet.bit false)))
      (decide (pair.2 = ProtocolMatrix.dataToken (alphabet.bit true))) (Fin.natAdd n index))
    (fun index => EncryptedEfficientMatrix.liftLiteral
      (mappedLiteral alphabet (fun token => literal (finProdFinEquiv (index, token))) pair.2)) pair.1

theorem inputLiteral_correct {n : ℕ} (alphabet : Alphabet vocabulary outputCard)
    (literal : Fin (front * 2) → Autoregressive.ContextLiteral n) (input : Bits n)
    (plain : Fin front → Fin 2) (seed : Bits seedLength)
    (correct : ∀ wire, (literal wire).eval input = RoutedMatrix.promptInput plain wire)
    (wire : Fin ((seedLength + front) * (vocabulary + 1))) :
    (inputLiteral alphabet literal seedLength wire).eval (Fin.append input seed) = inputEncoding alphabet plain seed wire := by
  rw [inputEncoding_eq]
  obtain ⟨⟨position, token⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · simp only [Fin.addCases_left, EfficientMatrix.eval_bitLiteral, Fin.append_right]
    cases h : seed index <;> simp [h]
  · simp only [Fin.addCases_right, EncryptedEfficientMatrix.eval_liftLiteral]
    apply mappedLiteral_correct
    intro value
    simpa only [RoutedMatrix.promptInput, Equiv.symm_apply_apply] using correct (finProdFinEquiv (index, value))

def headCount (heads width locality : ℕ) := EncryptedMatrix.headCount 2 heads locality + EncryptedReadout.readHeads width locality
def opcodeCount (heads opcodes width vocabulary outputCard locality : ℕ) :=
  ScheduleRecoding.opcodeCount
    (EncryptedMatrix.opcodeCount 2 heads opcodes locality + EncryptedFiniteReadout.readOpcodes width outputCard locality)
    (headCount heads width locality) vocabulary (EncryptedMatrix.packetCount 2 + outputCard) + 1

theorem one_layer (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) :
    (model alphabet original originalTransition generator sources decode label).architecture.layers = 1 := rfl

theorem precision_fixed (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) :
    (model alphabet original originalTransition generator sources decode label).parameters.scalarBits =
      RoutedMatrix.precision (vocabulary + 1) (headCount heads width locality)
        (opcodeCount heads opcodes width vocabulary outputCard locality) := rfl

theorem context_length (alphabet : Alphabet vocabulary outputCard) (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (label : Fin vocabulary → Bool) :
    (model alphabet original originalTransition generator sources decode label).architecture.contextLength =
      seedLength + front + steps + extra + 1 := by
  change seedLength + front + (steps + extra + 1) = _
  omega

theorem polynomial_resources {fronts times extras seedLengths : ℕ → ℕ}
    (alphabet : Alphabet vocabulary outputCard) (originals : ∀ n, Schedule (fronts n) (times n) heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1))
    (sources : ∀ n, Fin (extras n + 1) → Fin width → Fin (times n))
    (decode : ∀ n, Fin (extras n + 1) → Bits width → Fin outputCard) (label : Fin vocabulary → Bool)
    (coefficient exponent : ℕ)
    (bounded : ∀ n, (model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.contextLength + 1 ≤
      coefficient * (n + 1) ^ exponent) :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ exponent ∧
      (model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ (2 * exponent) := by
  let H := headCount heads width generator.locality
  let D := RoutedMatrix.dimensionConstant (vocabulary + 1) H (opcodeCount heads opcodes width vocabulary outputCard generator.locality)
  let P := 3 * (vocabulary + 1) * D + 4 * (3 * H + 2) * D ^ 2
  refine ⟨2 * D * coefficient, P * coefficient ^ 2, ?_⟩
  intro n
  have hdim : (model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.hiddenWidth ≤
      2 * D * ((model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.contextLength + 1) :=
    RoutedMatrix.hidden_dimension_linear
  have hpar : (model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.parameterCount ≤
      P * ((model alphabet (originals n) originalTransition (generator.generator n) (sources n) (decode n) label).architecture.contextLength + 1) ^ 2 :=
    RoutedMatrix.parameter_count_quadratic
  constructor
  · exact hdim.trans (by nlinarith [Nat.mul_le_mul_left (2 * D) (bounded n)])
  · have hsquare := Nat.pow_le_pow_left (bounded n) 2
    have hmul := Nat.mul_le_mul_left P hsquare
    rw [mul_pow, ← pow_mul, Nat.mul_comm exponent 2] at hmul
    exact hpar.trans (by nlinarith)

end ExactEncryptedAlphabet
