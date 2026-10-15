import ScheduleRelabel
import FiniteProtocolPrivacy

/-!
# Native finite-alphabet outputs following encrypted binary reasoning

Each public output coordinate has its own fixed finite decoder. This covers
full group elements and self-delimiting output alphabets, not just Boolean
labels. Output decoders become finite opcodes in the actual shared matrices.
-/

noncomputable section
namespace EncryptedFiniteReadout
open TransformerAC0 Encryption RoutedSchedule
variable {front steps extra heads opcodes width outputCard seedLength locality codeWidth : ℕ}

def packet (value : Fin (EncryptedMatrix.packetCount 2)) : Fin (EncryptedMatrix.packetCount 2 + outputCard) :=
  Fin.castAdd outputCard value
def result (value : Fin outputCard) : Fin (EncryptedMatrix.packetCount 2 + outputCard) :=
  Fin.natAdd (EncryptedMatrix.packetCount 2) value
def project : Fin (EncryptedMatrix.packetCount 2 + outputCard) → Fin (EncryptedMatrix.packetCount 2) :=
  Fin.addCases id (fun _ => ⟨0, EncryptedMatrix.packet_positive 2⟩)
@[simp] theorem project_packet (value : Fin (EncryptedMatrix.packetCount 2)) : project (packet (outputCard := outputCard) value) = value := by
  simp [project, packet]

abbrev Rule (width outputCard locality : ℕ) := EncryptedReadout.Rules width locality × (Bits width → Fin outputCard)
noncomputable instance ruleFintype (width outputCard locality : ℕ) : Fintype (Rule width outputCard locality) := Fintype.ofFinite _
def readOpcodes (width outputCard locality : ℕ) := Fintype.card (Rule width outputCard locality)
def ruleCode : Rule width outputCard locality ≃ Fin (readOpcodes width outputCard locality) := Fintype.equivFin _

def readouts (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    ReadoutSchedule.Readouts (seedLength + front) steps extra (EncryptedReadout.readHeads width locality) (readOpcodes width outputCard locality) where
  source := (EncryptedReadout.readouts generator sources).source
  opcode output := ruleCode (fun bit => generator.truthTable (sources output bit).castSucc, decode output)

def readTransition (opcode : Fin (readOpcodes width outputCard locality))
    (selected : Fin (EncryptedReadout.readHeads width locality) → Fin (EncryptedMatrix.packetCount 2 + outputCard)) :=
  result ((ruleCode.symm opcode).2 (fun bit => xor
    (EncryptedMatrix.cipherValue (project (selected (EncryptedReadout.bitHead bit))) 1)
    ((ruleCode.symm opcode).1 bit (fun index => EncryptedMatrix.seedValue
      (project (selected (EncryptedReadout.seedHead bit index)))))))

def schedule (original : Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :=
  ReadoutSchedule.schedule (ProtocolEncryptedBinary.baseSchedule original generator) (readouts generator sources decode)

def run (original : Fin opcodes → (Fin heads → Fin 2) → Fin 2) :=
  ReadoutSchedule.transition
    (liftTransition (packet (outputCard := outputCard)) project (ProtocolEncryptedBinary.run (locality := locality) original (fun _ => false)))
    (readTransition (width := width) (locality := locality) (outputCard := outputCard))

def prompt (plain : Fin front → Fin 2) (seed : Bits seedLength) :=
  fun p => packet (outputCard := outputCard) (EncryptedMatrix.prompt plain seed p)

theorem prefix_lift (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (source : Fin (seedLength + front + steps)) :
    word (prompt (outputCard := outputCard) plain seed) steps
      (fun previous => token (ProtocolEncryptedBinary.baseSchedule original generator)
        (liftTransition packet project (ProtocolEncryptedBinary.run originalTransition (fun _ => false)))
        (prompt plain seed) previous.castSucc) source =
      packet (EncryptedReadout.prefixWord original originalTransition generator plain seed source) := by
  unfold prompt
  simp only [token_lift _ packet project project_packet, word_map]
  rfl

theorem read_correct (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (output : Fin (extra + 1)) :
    token (schedule original generator sources decode) (run originalTransition) (prompt plain seed)
      ⟨steps + output.val, by have h := output.isLt; omega⟩ =
      result (decode output (fun bit => EncryptedBinaryMatrix.plainTranscript original originalTransition plain (sources output bit))) := by
  unfold schedule run
  rw [ReadoutSchedule.read_correct]
  have hop : (readouts (front := front) generator sources decode).opcode output =
      ruleCode (fun bit => generator.truthTable (sources output bit).castSucc, decode output) := rfl
  simp only [readTransition, hop, Equiv.symm_apply_apply, prefix_lift, project_packet]
  congr 2
  funext bit
  change xor (EncryptedMatrix.cipherValue (EncryptedReadout.prefixWord original originalTransition generator plain seed
      ((EncryptedReadout.readouts generator sources).source output (EncryptedReadout.bitHead bit))) 1)
    (generator.truthTable (sources output bit).castSucc (fun index => EncryptedMatrix.seedValue
      (EncryptedReadout.prefixWord original originalTransition generator plain seed
        ((EncryptedReadout.readouts generator sources).source output (EncryptedReadout.seedHead bit index))))) = _
  rw [EncryptedReadout.read_bit]
  have hmask : (fun index => EncryptedMatrix.seedValue
      (EncryptedReadout.prefixWord original originalTransition generator plain seed
        ((EncryptedReadout.readouts (front := front) generator sources).source output (EncryptedReadout.seedHead bit index)))) =
      generator.localInput (sources output bit).castSucc seed := by
    funext index
    exact EncryptedReadout.read_seed original originalTransition generator sources plain seed output bit index
  rw [hmask, generator.truthTable_correct]
  simp [Bool.xor_assoc]

def model (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :=
  ProtocolMatrix.model (schedule original generator sources decode) (by have h := EncryptedMatrix.packet_positive 2; omega)
    (run originalTransition) (fun _ => false) steps (by omega)

def inputEncoding (plain : Fin front → Fin 2) (seed : Bits seedLength) :=
  RoutedMatrix.promptInput (fun p => ProtocolMatrix.dataToken (prompt (outputCard := outputCard) plain seed p))

theorem payload_correct (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (time : Fin steps) :
    (model original originalTransition generator sources decode).generatedToken (inputEncoding plain seed)
      ⟨time.val, by have h := time.isLt; omega⟩ =
      ProtocolMatrix.dataToken (packet (EncryptedBinaryMatrix.binaryPacket
        (xor (EncryptedBinaryMatrix.plainTranscript original originalTransition plain time) (generator.generate seed time.castSucc)))) := by
  rw [model, inputEncoding, ProtocolMatrix.generated_correct]
  have hnot : time.val ≠ steps := by have ht := time.isLt; omega
  simp only [ProtocolMatrix.target, hnot, ↓reduceIte]
  have ht : ProtocolMatrix.oldTime (steps := steps + extra) steps (by omega) ⟨time.val, by have h := time.isLt; omega⟩ =
      ReadoutSchedule.extendTime (extra := extra) time := by
    apply Fin.ext
    simp [ProtocolMatrix.oldTime, ReadoutSchedule.extendTime, Nat.le_of_lt time.isLt]
  rw [ht, schedule, run, ReadoutSchedule.prefix_correct]
  unfold prompt
  rw [token_lift _ packet project project_packet, EncryptedReadout.base_payload]

theorem output_correct (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) (output : Fin (extra + 1)) :
    (model original originalTransition generator sources decode).generatedToken (inputEncoding plain seed)
      ⟨steps + 1 + output.val, by have h := output.isLt; omega⟩ =
      ProtocolMatrix.dataToken (result (decode output (fun bit =>
        EncryptedBinaryMatrix.plainTranscript original originalTransition plain (sources output bit)))) := by
  rw [model, inputEncoding, ProtocolMatrix.generated_correct]
  have hnot : steps + 1 + output.val ≠ steps := by omega
  simp only [ProtocolMatrix.target, hnot, ↓reduceIte]
  have ht : ProtocolMatrix.oldTime (steps := steps + extra) steps (by omega)
      ⟨steps + 1 + output.val, by have h := output.isLt; omega⟩ = ⟨steps + output.val, by have h := output.isLt; omega⟩ := by
    apply Fin.ext
    simp [ProtocolMatrix.oldTime, show ¬steps + 1 + output.val ≤ steps by omega]
  rw [ht, read_correct]

theorem separator_generated (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    (model original originalTransition generator sources decode).generatedToken (inputEncoding plain seed)
      ⟨steps, by omega⟩ = ProtocolMatrix.separator (EncryptedMatrix.packetCount 2 + outputCard) :=
  ProtocolMatrix.separator_generated _ _ _ _ _ _ _

def legacyEncoding (encoding : Fin (EncryptedMatrix.packetCount 2 + outputCard + 1) → Bits codeWidth) :
    ProtocolSerialization.Encoding codeWidth :=
  Fin.lastCases (encoding (ProtocolMatrix.separator (EncryptedMatrix.packetCount 2 + outputCard)))
    (fun value => encoding (ProtocolMatrix.dataToken (packet value)))

def encodedTrace (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + outputCard + 1) → Bits codeWidth)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) : Bits ((steps + 1) * codeWidth) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  encoding ((model original originalTransition generator sources decode).generatedToken (inputEncoding plain seed)
    (Fin.castLE (by omega : steps + 1 ≤ steps + extra + 2) pair.1)) pair.2

theorem encodedTrace_eq_encode (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + outputCard + 1) → Bits codeWidth)
    (plain : Fin front → Fin 2) (seed : Bits seedLength) :
    encodedTrace original originalTransition generator sources decode encoding plain seed =
      ProtocolSerialization.encode (legacyEncoding encoding)
        (encryptedTrace (EncryptedBinaryMatrix.plainTranscript original originalTransition)
          (prefixGenerator generator.generate) plain seed) := by
  funext wire
  obtain ⟨⟨position, bit⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [encodedTrace, ProtocolSerialization.encode, Equiv.symm_apply_apply]
  refine Fin.lastCases ?_ (fun position => ?_) position
  · simp only [Fin.lastCases_last]
    simpa only [legacyEncoding, ProtocolMatrix.separator, Fin.lastCases_last] using congrArg (fun value => encoding value bit)
      (separator_generated original originalTransition generator sources decode plain seed)
  · simp only [Fin.lastCases_castSucc]
    simpa only [legacyEncoding, ProtocolMatrix.dataToken, Fin.lastCases_castSucc, encryptedTrace, prefixGenerator, bitXor] using congrArg (fun value => encoding value bit)
      (payload_correct original originalTransition generator sources decode plain seed position)

theorem no_readability_finite {Input : ℕ → Type*} [∀ n, Fintype (Input n)] [∀ n, Nonempty (Input n)]
    {seedLengths fronts times extras : ℕ → ℕ}
    (originals : ∀ n, Schedule (fronts n) (times n) heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (sources : ∀ n, Fin (extras n + 1) → Fin width → Fin (times n))
    (decode : ∀ n, Fin (extras n + 1) → Bits width → Fin outputCard)
    (prompts : ∀ n, Input n → Fin (fronts n) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1)) (secure : generator.IsPseudorandom)
    (encoding : Fin (EncryptedMatrix.packetCount 2 + outputCard + 1) → Bits codeWidth)
    (monitor : PolynomialMonitorFamily (fun n => (times n + 1) * codeWidth))
    (coefficient exponent : ℕ) (timeLength : ∀ n, times n ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Input n)) (predicate : Input n → Bool),
      predictionSuccess distribution
        (fun input seed => encodedTrace (originals n) originalTransition (generator.generator n) (sources n) (decode n) encoding (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hprivacy⟩ := PolynomialEncryption.no_readability_finite
    (suffix := fun _ => 1) generator secure
    (fun n input => EncryptedBinaryMatrix.plainTranscript (originals n) originalTransition (prompts n input))
    (ProtocolSerialization.pullbackMonitor (legacyEncoding encoding) monitor coefficient exponent timeLength)
    coefficient exponent timeLength
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  simpa only [predictionSuccess, encodedTrace_eq_encode, ProtocolSerialization.pullback_monitor] using hprivacy n distribution predicate

theorem one_layer (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    (model original originalTransition generator sources decode).architecture.layers = 1 := rfl

theorem heads_fixed (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    (model original originalTransition generator sources decode).architecture.heads =
      EncryptedMatrix.headCount 2 heads locality + EncryptedReadout.readHeads width locality := rfl

theorem precision_fixed (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    (model original originalTransition generator sources decode).parameters.scalarBits =
      RoutedMatrix.precision (EncryptedMatrix.packetCount 2 + outputCard + 1)
        (EncryptedMatrix.headCount 2 heads locality + EncryptedReadout.readHeads width locality)
        (EncryptedMatrix.opcodeCount 2 heads opcodes locality + readOpcodes width outputCard locality + 1) := rfl

theorem context_length (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    (model original originalTransition generator sources decode).architecture.contextLength =
      seedLength + front + steps + extra + 1 := by
  change seedLength + front + (steps + extra + 1) = _
  omega

def inputLiteral {n : ℕ} (literal : Fin (front * 2) → Autoregressive.ContextLiteral n) (seedLength outputCard : ℕ) :
    Fin ((seedLength + front) * (EncryptedMatrix.packetCount 2 + outputCard + 1)) → Autoregressive.ContextLiteral (n + seedLength) :=
  fun wire =>
    let pair := finProdFinEquiv.symm wire
    Fin.lastCases (.constant false)
      (Fin.addCases
        (fun value => ProtocolEncryptedBinary.inputLiteral literal seedLength (finProdFinEquiv (pair.1, value.castSucc)))
        (fun _ => .constant false)) pair.2

theorem inputLiteral_correct {n : ℕ} (literal : Fin (front * 2) → Autoregressive.ContextLiteral n)
    (input : Bits n) (plain : Fin front → Fin 2) (seed : Bits seedLength)
    (correct : ∀ wire, (literal wire).eval input = RoutedMatrix.promptInput plain wire)
    (wire : Fin ((seedLength + front) * (EncryptedMatrix.packetCount 2 + outputCard + 1))) :
    (inputLiteral literal seedLength outputCard wire).eval (Fin.append input seed) =
      inputEncoding (outputCard := outputCard) plain seed wire := by
  obtain ⟨⟨position, value⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [inputLiteral, inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply]
  refine Fin.lastCases ?_ (fun value => ?_) value
  · have hne : Fin.last (EncryptedMatrix.packetCount 2 + outputCard) ≠ (prompt (outputCard := outputCard) plain seed position).castSucc := by
      intro heq
      have hval := congrArg Fin.val heq
      have hp := (prompt (outputCard := outputCard) plain seed position).isLt
      change EncryptedMatrix.packetCount 2 + outputCard = (prompt (outputCard := outputCard) plain seed position).val at hval
      omega
    simp [Autoregressive.ContextLiteral.eval, ProtocolMatrix.dataToken, hne]
  · simp only [Fin.lastCases_castSucc]
    refine Fin.addCases (fun value => ?_) (fun value => ?_) value
    · simp only [Fin.addCases_left, ProtocolEncryptedBinary.inputLiteral_correct _ _ _ _ correct,
        ProtocolEncryptedBinary.inputEncoding, RoutedMatrix.promptInput, Equiv.symm_apply_apply,
        prompt, packet, ProtocolMatrix.dataToken, Fin.castSucc_inj, Fin.castAdd_inj]
    · simp only [Fin.addCases_right, Autoregressive.ContextLiteral.eval, prompt, packet, ProtocolMatrix.dataToken,
        Fin.castSucc_inj]
      have hne : Fin.natAdd (EncryptedMatrix.packetCount 2) value ≠
          Fin.castAdd outputCard (EncryptedMatrix.prompt plain seed position) := by
        intro heq
        have h := congrArg Fin.val heq
        have hp := (EncryptedMatrix.prompt plain seed position).isLt
        change EncryptedMatrix.packetCount 2 + value.val = (EncryptedMatrix.prompt plain seed position).val at h
        omega
      simp [hne]

theorem dimension_linear (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    (model original originalTransition generator sources decode).architecture.hiddenWidth ≤
      2 * RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + outputCard + 1)
        (EncryptedMatrix.headCount 2 heads locality + EncryptedReadout.readHeads width locality)
        (EncryptedMatrix.opcodeCount 2 heads opcodes locality + readOpcodes width outputCard locality + 1) *
      ((model original originalTransition generator sources decode).architecture.contextLength + 1) :=
  RoutedMatrix.hidden_dimension_linear

theorem parameters_quadratic (original : Schedule front steps heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : LocalGenerator seedLength (steps + 1) locality)
    (sources : Fin (extra + 1) → Fin width → Fin steps) (decode : Fin (extra + 1) → Bits width → Fin outputCard) :
    let D := RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + outputCard + 1)
      (EncryptedMatrix.headCount 2 heads locality + EncryptedReadout.readHeads width locality)
      (EncryptedMatrix.opcodeCount 2 heads opcodes locality + readOpcodes width outputCard locality + 1)
    (model original originalTransition generator sources decode).architecture.parameterCount ≤
      (3 * (EncryptedMatrix.packetCount 2 + outputCard + 1) * D +
        4 * (3 * (EncryptedMatrix.headCount 2 heads locality + EncryptedReadout.readHeads width locality) + 2) * D ^ 2) *
      ((model original originalTransition generator sources decode).architecture.contextLength + 1) ^ 2 :=
  RoutedMatrix.parameter_count_quadratic

theorem polynomial_resources {fronts times extras seedLengths : ℕ → ℕ}
    (originals : ∀ n, Schedule (fronts n) (times n) heads opcodes)
    (originalTransition : Fin opcodes → (Fin heads → Fin 2) → Fin 2)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n + 1))
    (sources : ∀ n, Fin (extras n + 1) → Fin width → Fin (times n))
    (decode : ∀ n, Fin (extras n + 1) → Bits width → Fin outputCard)
    (coefficient exponent : ℕ)
    (bounded : ∀ n, (model (originals n) originalTransition (generator.generator n) (sources n) (decode n)).architecture.contextLength + 1 ≤
      coefficient * (n + 1) ^ exponent) :
    ∃ dimensionCoefficient parameterCoefficient : ℕ, ∀ n,
      (model (originals n) originalTransition (generator.generator n) (sources n) (decode n)).architecture.hiddenWidth ≤
        dimensionCoefficient * (n + 1) ^ exponent ∧
      (model (originals n) originalTransition (generator.generator n) (sources n) (decode n)).architecture.parameterCount ≤
        parameterCoefficient * (n + 1) ^ (2 * exponent) := by
  let H := EncryptedMatrix.headCount 2 heads generator.locality + EncryptedReadout.readHeads width generator.locality
  let D := RoutedMatrix.dimensionConstant (EncryptedMatrix.packetCount 2 + outputCard + 1) H
    (EncryptedMatrix.opcodeCount 2 heads opcodes generator.locality + readOpcodes width outputCard generator.locality + 1)
  let P := 3 * (EncryptedMatrix.packetCount 2 + outputCard + 1) * D + 4 * (3 * H + 2) * D ^ 2
  refine ⟨2 * D * coefficient, P * coefficient ^ 2, ?_⟩
  intro n
  have hdim := dimension_linear (originals n) originalTransition (generator.generator n) (sources n) (decode n)
  have hpar := parameters_quadratic (originals n) originalTransition (generator.generator n) (sources n) (decode n)
  change _ ≤ 2 * D * _ at hdim
  change _ ≤ P * _ ^ 2 at hpar
  constructor
  · exact hdim.trans (by nlinarith [Nat.mul_le_mul_left (2 * D) (bounded n)])
  · have hsquare := Nat.pow_le_pow_left (bounded n) 2
    have hmul := Nat.mul_le_mul_left P hsquare
    rw [mul_pow, ← pow_mul, Nat.mul_comm exponent 2] at hmul
    exact hpar.trans (by nlinarith)

end EncryptedFiniteReadout
