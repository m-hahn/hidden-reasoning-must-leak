import RoutedSchedule
import LocalPRG
import PolynomialEncryption

/-!
# On-the-fly encryption by one shared numerical matrix Transformer

Only plaintext prompt tokens and raw seed bits are initialized. Additional
causal heads retrieve the seed neighborhoods for the preceding tokens and
the current token. A finite MLP decrypts, executes the local transition, and
encrypts its output. All pad truth tables and source positions are static.
-/

noncomputable section
namespace EncryptedMatrix
open TransformerAC0 Encryption

variable {front steps heads opcodes vocabulary seedLength locality : ℕ}

abbrev Packet (vocabulary : ℕ) := Fin vocabulary ⊕ (Bool ⊕ (Bits vocabulary ⊕ Bool))
def packetCount (vocabulary : ℕ) : ℕ := Fintype.card (Packet vocabulary)
def packetCode : Packet vocabulary ≃ Fin (packetCount vocabulary) := Fintype.equivFin _

def plainPacket (token : Fin vocabulary) : Fin (packetCount vocabulary) := packetCode (.inl token)
def seedPacket (vocabulary : ℕ) (bit : Bool) : Fin (packetCount vocabulary) := packetCode (.inr (.inl bit))
def cipherPacket (word : Bits vocabulary) : Fin (packetCount vocabulary) := packetCode (.inr (.inr (.inl word)))
def answerPacket (vocabulary : ℕ) (bit : Bool) : Fin (packetCount vocabulary) := packetCode (.inr (.inr (.inr bit)))

def seedValue (packet : Fin (packetCount vocabulary)) : Bool :=
  match packetCode.symm packet with
  | .inr (.inl bit) => bit
  | _ => false

def cipherValue (packet : Fin (packetCount vocabulary)) : Bits vocabulary :=
  match packetCode.symm packet with
  | .inr (.inr (.inl word)) => word
  | _ => fun _ => false

def answerValue (packet : Fin (packetCount vocabulary)) : Bool :=
  match packetCode.symm packet with
  | .inr (.inr (.inr bit)) => bit
  | _ => false

def decrypt (hv : 0 < vocabulary) (packet : Fin (packetCount vocabulary)) (pad : Bits vocabulary) : Fin vocabulary :=
  match packetCode.symm packet with
  | .inl token => token
  | .inr (.inr (.inl cipher)) => RoutedMatrix.decodeIndicator hv (bitXor cipher pad)
  | _ => ⟨0, hv⟩

theorem packet_positive (vocabulary : ℕ) : 0 < packetCount vocabulary := by
  letI : Nonempty (Packet vocabulary) := ⟨.inr (.inl false)⟩
  exact Fintype.card_pos

@[simp] theorem seedValue_seedPacket (bit : Bool) : seedValue (seedPacket vocabulary bit) = bit := by
  simp [seedValue, seedPacket]

@[simp] theorem cipherValue_cipherPacket (word : Bits vocabulary) : cipherValue (cipherPacket word) = word := by
  simp [cipherValue, cipherPacket]

@[simp] theorem answerValue_answerPacket (bit : Bool) : answerValue (answerPacket vocabulary bit) = bit := by
  simp [answerValue, answerPacket]

@[simp] theorem decrypt_plainPacket (hv : 0 < vocabulary) (token : Fin vocabulary) (pad : Bits vocabulary) :
    decrypt hv (plainPacket token) pad = token := by simp [decrypt, plainPacket]

theorem decrypt_cipherPacket (hv : 0 < vocabulary) (token : Fin vocabulary) (pad : Bits vocabulary) :
    decrypt hv (cipherPacket (bitXor (RoutedMatrix.indicator token) pad)) pad = token := by
  simp only [decrypt, cipherPacket, Equiv.symm_apply_apply, bitXor_right_involutive]
  exact RoutedMatrix.decodeIndicator_indicator hv token

def headCount (vocabulary heads locality : ℕ) : ℕ := heads + (heads + 1) * vocabulary * locality

def sourceHead (head : Fin heads) : Fin (headCount vocabulary heads locality) :=
  Fin.castAdd ((heads + 1) * vocabulary * locality) head

def seedHead (block : Fin (heads + 1)) (bit : Fin vocabulary) (index : Fin locality) :
    Fin (headCount vocabulary heads locality) :=
  Fin.natAdd heads (finProdFinEquiv (finProdFinEquiv (block, bit), index))

abbrev Rules (vocabulary heads locality : ℕ) := Fin (heads + 1) → Fin vocabulary → Bits locality → Bool
abbrev Opcode (vocabulary heads opcodes locality : ℕ) := Fin opcodes × (Rules vocabulary heads locality × Bool)

noncomputable instance opcodeFintype (vocabulary heads opcodes locality : ℕ) :
    Fintype (Opcode vocabulary heads opcodes locality) := Fintype.ofFinite _

def opcodeCount (vocabulary heads opcodes locality : ℕ) : ℕ := Fintype.card (Opcode vocabulary heads opcodes locality)
def opcodeCode : Opcode vocabulary heads opcodes locality ≃ Fin (opcodeCount vocabulary heads opcodes locality) :=
  Fintype.equivFin _

theorem opcode_positive (ho : 0 < opcodes) : 0 < opcodeCount vocabulary heads opcodes locality := by
  letI : Nonempty (Fin opcodes) := ⟨⟨0, ho⟩⟩
  exact Fintype.card_pos

def padIndex (time : Fin (steps + 1)) (bit : Fin vocabulary) : Fin (steps * vocabulary + vocabulary) :=
  Fin.cast (by ring) (finProdFinEquiv (time, bit))

def pad (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (seed : Bits seedLength) (time : Fin (steps + 1)) : Bits vocabulary :=
  fun bit => generator.generate seed (padIndex time bit)

def sourceTime (time : Fin (steps + 1)) (source : Fin (front + time.val)) : Fin (steps + 1) :=
  ⟨source.val - front, by have hs := source.isLt; have ht := time.isLt; omega⟩

def maskTime (schedule : RoutedSchedule.Schedule front steps heads opcodes) (time : Fin (steps + 1)) :
    Fin (heads + 1) → Fin (steps + 1) :=
  Fin.lastCases time (fun head => sourceTime time (schedule.source time head))

def opcodeAt (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (time : Fin (steps + 1)) : Opcode vocabulary heads opcodes locality :=
  (schedule.opcode time, ((fun block bit => generator.truthTable (padIndex (maskTime schedule time block) bit)),
    decide (time.val = steps)))

def masks (rules : Rules vocabulary heads locality)
    (selected : Fin (headCount vocabulary heads locality) → Fin (packetCount vocabulary))
    (block : Fin (heads + 1)) : Bits vocabulary := fun bit =>
  rules block bit (fun index => seedValue (selected (seedHead block bit index)))

def transition (hv : 0 < vocabulary)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (opcode : Fin (opcodeCount vocabulary heads opcodes locality))
    (selected : Fin (headCount vocabulary heads locality) → Fin (packetCount vocabulary)) : Fin (packetCount vocabulary) :=
  let data := opcodeCode.symm opcode
  let plain := plainTransition data.1
    (fun head => decrypt hv (selected (sourceHead head)) (masks data.2.1 selected head.castSucc))
  if data.2.2 then answerPacket vocabulary (label plain)
  else cipherPacket (bitXor (RoutedMatrix.indicator plain) (masks data.2.1 selected (Fin.last heads)))

def shifted (schedule : RoutedSchedule.Schedule front steps heads opcodes) :
    RoutedSchedule.Schedule (seedLength + front) steps heads opcodes where
  front_positive := by have hf := schedule.front_positive; omega
  source time head := ⟨seedLength + (schedule.source time head).val, by
    have hs := (schedule.source time head).isLt; omega⟩
  opcode := schedule.opcode

def routeAt (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (time : Fin (steps + 1)) : Fin (headCount vocabulary heads locality) → Fin (seedLength + front + steps) :=
  Fin.addCases (fun head => ⟨seedLength + (schedule.source time head).val, by
      have hs := (schedule.source time head).isLt; have ht := time.isLt; omega⟩)
    (fun index =>
      let pair := finProdFinEquiv.symm index
      let blockBit := finProdFinEquiv.symm pair.1
      let seedIndex := generator.dependency (padIndex (maskTime schedule time blockBit.1) blockBit.2) pair.2
      ⟨seedIndex.val, by have hi := seedIndex.isLt; have hf := schedule.front_positive; omega⟩)

theorem routeAt_le (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (position : Fin (seedLength + front + steps)) (time : Fin (steps + 1))
    (hactive : RoutedSchedule.activeTime (shifted (seedLength := seedLength) schedule) position = some time)
    (head : Fin (headCount vocabulary heads locality)) : routeAt schedule generator time head ≤ position := by
  have hp := RoutedSchedule.activeTime_some (shifted (seedLength := seedLength) schedule) position time hactive
  have hf := schedule.front_positive
  refine Fin.addCases (fun h => ?_) (fun i => ?_) head
  · simp only [routeAt, Fin.addCases_left]
    change seedLength + (schedule.source time h).val ≤ position.val
    have hs := (schedule.source time h).isLt
    omega
  · simp only [routeAt, Fin.addCases_right]
    have hi := (generator.dependency
      (padIndex (maskTime schedule time (finProdFinEquiv.symm (finProdFinEquiv.symm i).1).1)
        (finProdFinEquiv.symm (finProdFinEquiv.symm i).1).2) (finProdFinEquiv.symm i).2).isLt
    change _ ≤ position.val
    dsimp only
    omega

def plan (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality) :
    RoutedMatrix.Plan (packetCount vocabulary) (seedLength + front + steps)
      (headCount vocabulary heads locality) (opcodeCount vocabulary heads opcodes locality) where
  route position head := match RoutedSchedule.activeTime (shifted (seedLength := seedLength) schedule) position with
    | none => ⟨0, by have hf := schedule.front_positive; omega⟩
    | some time => routeAt schedule generator time head
  causal := by
    intro position head
    cases hactive : RoutedSchedule.activeTime (shifted (seedLength := seedLength) schedule) position with
    | none => exact Nat.zero_le _
    | some time => exact routeAt_le schedule generator position time hactive head
  opcode position := opcodeCode (opcodeAt schedule generator
    ((RoutedSchedule.activeTime (shifted (seedLength := seedLength) schedule) position).getD ⟨0, Nat.zero_lt_succ _⟩))

def queryPosition (schedule : RoutedSchedule.Schedule front steps heads opcodes) (time : Fin (steps + 1)) :
    Fin (seedLength + front + steps) := RoutedSchedule.position (shifted schedule) time

@[simp] theorem plan_route (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (time : Fin (steps + 1)) (head : Fin (headCount vocabulary heads locality)) :
    (plan schedule generator).route (queryPosition (seedLength := seedLength) schedule time) head = routeAt schedule generator time head := by
  simp only [plan, queryPosition, RoutedSchedule.activeTime_position]

@[simp] theorem plan_opcode (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (time : Fin (steps + 1)) :
    (plan schedule generator).opcode (queryPosition (seedLength := seedLength) schedule time) = opcodeCode (opcodeAt schedule generator time) := by
  simp only [plan, queryPosition, RoutedSchedule.activeTime_position, Option.getD_some]

def prompt (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) : Fin (seedLength + front) → Fin (packetCount vocabulary) :=
  Fin.addCases (fun index => seedPacket vocabulary (seed index)) (fun index => plainPacket (plain index))

def target (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1)) : Fin (packetCount vocabulary) :=
  if time.val = steps then answerPacket vocabulary (label (RoutedSchedule.token schedule plainTransition plain time))
  else cipherPacket (bitXor (RoutedMatrix.indicator (RoutedSchedule.token schedule plainTransition plain time)) (pad generator seed time))

def context (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1)) :
    Fin (seedLength + front + steps) → Fin (packetCount vocabulary) :=
  RoutedMatrix.contextWord (packet_positive vocabulary) (prompt plain seed) time.val
    (fun previous => target schedule plainTransition label generator plain seed ⟨previous.val, previous.isLt.trans time.isLt⟩)

theorem context_prompt (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1))
    (position : Fin (seedLength + front + steps)) (hposition : position.val < seedLength + front) :
    context schedule plainTransition label generator plain seed time position = prompt plain seed ⟨position.val, hposition⟩ := by
  simp only [context, RoutedMatrix.contextWord, dif_pos hposition]

theorem context_previous (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1))
    (position : Fin (seedLength + front + steps))
    (hposition : seedLength + front ≤ position.val) (hprevious : position.val - (seedLength + front) < time.val) :
    context schedule plainTransition label generator plain seed time position =
      target schedule plainTransition label generator plain seed
        ⟨position.val - (seedLength + front), hprevious.trans time.isLt⟩ := by
  simp only [context, RoutedMatrix.contextWord, dif_neg (by omega : ¬position.val < seedLength + front), dif_pos hprevious]

theorem routeAt_seedHead (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (time : Fin (steps + 1)) (block : Fin (heads + 1)) (bit : Fin vocabulary) (index : Fin locality) :
    (routeAt schedule generator time (seedHead block bit index)).val =
      (generator.dependency (padIndex (maskTime schedule time block) bit) index).val := by
  simp only [routeAt, seedHead, Fin.addCases_right, Equiv.symm_apply_apply]

theorem read_seed (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1))
    (block : Fin (heads + 1)) (bit : Fin vocabulary) (index : Fin locality) :
    seedValue (context schedule plainTransition label generator plain seed time
      (routeAt schedule generator time (seedHead block bit index))) =
      seed (generator.dependency (padIndex (maskTime schedule time block) bit) index) := by
  have hr := routeAt_seedHead schedule generator time block bit index
  rw [context_prompt schedule plainTransition label generator plain seed time _
    (by rw [hr]; have hi := (generator.dependency (padIndex (maskTime schedule time block) bit) index).isLt; omega)]
  have hp : (⟨(routeAt schedule generator time (seedHead block bit index)).val,
      by rw [hr]; have hi := (generator.dependency (padIndex (maskTime schedule time block) bit) index).isLt; omega⟩ :
      Fin (seedLength + front)) = Fin.castAdd front
      (generator.dependency (padIndex (maskTime schedule time block) bit) index) := by
    apply Fin.ext
    exact hr
  rw [hp]
  simp only [prompt, Fin.addCases_left, seedValue_seedPacket]

theorem masks_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1))
    (block : Fin (heads + 1)) :
    masks (opcodeAt schedule generator time).2.1
      (fun head => context schedule plainTransition label generator plain seed time (routeAt schedule generator time head)) block =
        pad generator seed (maskTime schedule time block) := by
  funext bit
  simp only [masks, opcodeAt, pad]
  have hlocal : (fun index => seedValue (context schedule plainTransition label generator plain seed time
      (routeAt schedule generator time (seedHead block bit index)))) =
      generator.localInput (padIndex (maskTime schedule time block) bit) seed := by
    funext index
    exact read_seed schedule plainTransition label generator plain seed time block bit index
  rw [hlocal]
  exact generator.truthTable_correct _ seed

def sourcePosition (time : Fin (steps + 1)) (source : Fin (front + time.val)) : Fin (seedLength + front + steps) :=
  ⟨seedLength + source.val, by have hs := source.isLt; have ht := time.isLt; omega⟩

@[simp] theorem routeAt_sourceHead (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (time : Fin (steps + 1)) (head : Fin heads) :
    routeAt schedule generator time (sourceHead head) = sourcePosition time (schedule.source time head) := by
  simp only [routeAt, sourceHead, Fin.addCases_left]
  rfl

@[simp] theorem maskTime_source (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (time : Fin (steps + 1)) (head : Fin heads) :
    maskTime schedule time head.castSucc = sourceTime time (schedule.source time head) := by
  simp [maskTime]

@[simp] theorem maskTime_current (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (time : Fin (steps + 1)) : maskTime schedule time (Fin.last heads) = time := by simp [maskTime]

theorem read_source (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1))
    (source : Fin (front + time.val)) (hv : 0 < vocabulary) :
    decrypt hv (context schedule plainTransition label generator plain seed time (sourcePosition time source))
      (pad generator seed (sourceTime time source)) =
      RoutedSchedule.word plain time.val
        (fun previous => RoutedSchedule.token schedule plainTransition plain ⟨previous.val, previous.isLt.trans time.isLt⟩) source := by
  refine Fin.addCases (fun p => ?_) (fun previous => ?_) source
  · rw [context_prompt schedule plainTransition label generator plain seed time _
      (by change seedLength + p.val < seedLength + front; have hp := p.isLt; omega)]
    have hp : (⟨(sourcePosition time (Fin.castAdd time.val p)).val,
        by change seedLength + p.val < seedLength + front; have hp := p.isLt; omega⟩ : Fin (seedLength + front)) =
        Fin.natAdd seedLength p := rfl
    rw [hp]
    simp only [prompt, Fin.addCases_right, decrypt_plainPacket, RoutedSchedule.word, Fin.addCases_left]
  · rw [context_previous schedule plainTransition label generator plain seed time _
      (by change seedLength + front ≤ seedLength + (front + previous.val); omega)
      (by change seedLength + (front + previous.val) - (seedLength + front) < time.val; have hp := previous.isLt; omega)]
    have hpos : (sourcePosition (seedLength := seedLength) time (Fin.natAdd front previous)).val - (seedLength + front) =
        previous.val := by change seedLength + (front + previous.val) - (seedLength + front) = previous.val; omega
    have hprev : sourceTime time (Fin.natAdd front previous) =
        (⟨previous.val, previous.isLt.trans time.isLt⟩ : Fin (steps + 1)) := by apply Fin.ext; simp [sourceTime]
    have hnotlast : previous.val ≠ steps := by have hp := previous.isLt; have ht := time.isLt; omega
    simp only [target, hpos, hprev, if_neg hnotlast, RoutedSchedule.word, Fin.addCases_right]
    exact decrypt_cipherPacket hv _ _

/-- The finite local matrix table computes the generator neighborhoods,
decrypts its attended values, executes one plaintext instruction, then
encrypts the new token. The final Boolean answer is not ciphertext. -/
theorem step_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (label : Fin vocabulary → Bool)
    (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1)) (hv : 0 < vocabulary) :
    transition hv plainTransition label (opcodeCode (opcodeAt schedule generator time))
      (fun head => context schedule plainTransition label generator plain seed time (routeAt schedule generator time head)) =
        target schedule plainTransition label generator plain seed time := by
  unfold transition
  simp only [Equiv.symm_apply_apply, masks_correct]
  have hdecoded : (fun head => decrypt hv
      (context schedule plainTransition label generator plain seed time (routeAt schedule generator time (sourceHead head)))
      (pad generator seed (maskTime schedule time head.castSucc))) =
      (fun head => RoutedSchedule.word plain time.val
        (fun previous => RoutedSchedule.token schedule plainTransition plain ⟨previous.val, previous.isLt.trans time.isLt⟩)
        (schedule.source time head)) := by
    funext head
    rw [routeAt_sourceHead, maskTime_source]
    exact read_source schedule plainTransition label generator plain seed time _ hv
  rw [hdecoded]
  simp only [opcodeAt, maskTime_current]
  have hplain : plainTransition (schedule.opcode time)
      (fun head => RoutedSchedule.word plain time.val
        (fun previous => RoutedSchedule.token schedule plainTransition plain ⟨previous.val, previous.isLt.trans time.isLt⟩)
        (schedule.source time head)) = RoutedSchedule.token schedule plainTransition plain time := by
    rw [RoutedSchedule.token]
  rw [hplain]
  simp only [target, decide_eq_true_eq]

theorem plainOpcodes_positive (schedule : RoutedSchedule.Schedule front steps heads opcodes) : 0 < opcodes := by
  have h := (schedule.opcode ⟨0, Nat.zero_lt_succ _⟩).isLt
  omega

def localMap (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) :
    Bits (RoutedMatrix.featureCount (packetCount vocabulary) (headCount vocabulary heads locality)
      (opcodeCount vocabulary heads opcodes locality)) → Fin (packetCount vocabulary) :=
  RoutedMatrix.transitionMap (packet_positive vocabulary) (opcode_positive (plainOpcodes_positive schedule))
    (transition hv plainTransition label)

def model (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality) :
    CausalAutoregressive.Model
      (RoutedMatrix.architecture (packetCount vocabulary) (seedLength + front + steps)
        (headCount vocabulary heads locality) (opcodeCount vocabulary heads opcodes locality)) (seedLength + front) steps :=
  RoutedMatrix.causalModel (plan schedule generator) (localMap schedule hv plainTransition label) answerValue
    (packet_positive vocabulary) (by have hf := schedule.front_positive; omega) le_rfl

theorem routed_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1)) :
    RoutedMatrix.routedToken (plan schedule generator) (localMap schedule hv plainTransition label)
      (packet_positive vocabulary) (by have hf := schedule.front_positive; omega) le_rfl (prompt plain seed) time =
        target schedule plainTransition label generator plain seed time := by
  induction ht : time.val using Nat.strong_induction_on generalizing time with
  | h n ih =>
      rw [RoutedMatrix.routedToken]
      have hprevious : (fun previous : Fin time.val =>
          RoutedMatrix.routedToken (plan schedule generator) (localMap schedule hv plainTransition label)
            (packet_positive vocabulary) (by have hf := schedule.front_positive; omega) le_rfl (prompt plain seed)
            ⟨previous.val, previous.isLt.trans time.isLt⟩) =
          (fun previous : Fin time.val => target schedule plainTransition label generator plain seed
            ⟨previous.val, previous.isLt.trans time.isLt⟩) := by
        funext previous
        exact ih previous.val (by omega) _ rfl
      rw [hprevious]
      change localMap schedule hv plainTransition label
        (RoutedMatrix.features (plan schedule generator) (context schedule plainTransition label generator plain seed time)
          (queryPosition (seedLength := seedLength) schedule time)) = _
      unfold localMap
      rw [RoutedMatrix.transitionMap_features, plan_opcode]
      simp_rw [plan_route]
      exact step_correct schedule plainTransition label generator plain seed time hv

/-- The actual greedy autoregressive driver emits encrypted events and the
final plaintext answer. It is not given a precomputed encrypted transcript. -/
theorem generated_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin (steps + 1)) :
    (model schedule hv plainTransition label generator).generatedToken (RoutedMatrix.promptInput (prompt plain seed)) time =
      target schedule plainTransition label generator plain seed time := by
  unfold model
  rw [RoutedMatrix.autoregressive_correct]
  exact routed_correct schedule hv plainTransition label generator plain seed time

theorem output_correct (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) :
    (model schedule hv plainTransition label generator).answer (RoutedMatrix.promptInput (prompt plain seed)) =
      label (RoutedSchedule.token schedule plainTransition plain (Fin.last steps)) := by
  unfold CausalAutoregressive.Model.answer
  rw [generated_correct]
  change answerValue (target schedule plainTransition label generator plain seed (Fin.last steps)) = _
  simp only [target, Fin.val_last, if_true, answerValue_answerPacket]

def plainTranscript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary) (plain : Fin front → Fin vocabulary) :
    Bits (steps * vocabulary) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  RoutedMatrix.indicator (RoutedSchedule.token schedule plainTransition plain pair.1.castSucc) pair.2

def transcript (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) : Bits (steps * vocabulary) := fun wire =>
  let pair := finProdFinEquiv.symm wire
  cipherValue ((model schedule hv plainTransition label generator).transcript (RoutedMatrix.promptInput (prompt plain seed)) pair.1) pair.2

@[simp] theorem padIndex_castSucc (time : Fin steps) (bit : Fin vocabulary) :
    padIndex time.castSucc bit = Fin.castLE (Nat.le_add_right (steps * vocabulary) vocabulary) (finProdFinEquiv (time, bit)) := by
  apply Fin.ext
  rfl

/-- The visible ciphertext bits emitted by the numerical Transformer are
exactly plaintext XOR the specified PRG prefix. This bridges execution to
the already verified security reduction. -/
theorem transcript_eq_encryptedTrace (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) :
    transcript schedule hv plainTransition label generator plain seed =
      encryptedTrace (plainTranscript schedule plainTransition) (prefixGenerator generator.generate) plain seed := by
  funext wire
  obtain ⟨⟨time, bit⟩, rfl⟩ := finProdFinEquiv.surjective wire
  simp only [transcript, Equiv.symm_apply_apply, CausalAutoregressive.Model.transcript, generated_correct]
  have hnotlast : time.castSucc.val ≠ steps := by change time.val ≠ steps; have h := time.isLt; omega
  simp only [target, if_neg hnotlast, cipherValue_cipherPacket, bitXor, pad, encryptedTrace,
    plainTranscript, prefixGenerator, Fin.take, Equiv.symm_apply_apply, padIndex_castSucc]

theorem full_transcript_reconstructible (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality)
    (plain : Fin front → Fin vocabulary) (seed : Bits seedLength) (time : Fin steps) :
    (model schedule hv plainTransition label generator).transcript (RoutedMatrix.promptInput (prompt plain seed)) time =
      cipherPacket (fun bit => transcript schedule hv plainTransition label generator plain seed (finProdFinEquiv (time, bit))) := by
  simp only [CausalAutoregressive.Model.transcript, generated_correct]
  have hnotlast : time.castSucc.val ≠ steps := by change time.val ≠ steps; have h := time.isLt; omega
  simp only [target, if_neg hnotlast]
  congr 1
  funext bit
  simp only [transcript, Equiv.symm_apply_apply, CausalAutoregressive.Model.transcript, generated_correct,
    target, if_neg hnotlast, cipherValue_cipherPacket]

theorem fixed_precision (schedule : RoutedSchedule.Schedule front steps heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (generator : LocalGenerator seedLength (steps * vocabulary + vocabulary) locality) :
    (model schedule hv plainTransition label generator).parameters.scalarBits =
      RoutedMatrix.precision (packetCount vocabulary) (headCount vocabulary heads locality)
        (opcodeCount vocabulary heads opcodes locality) := rfl

theorem packet_card (vocabulary : ℕ) : packetCount vocabulary = vocabulary + 2 ^ vocabulary + 4 := by
  simp [packetCount, Packet, Bits]
  omega

theorem one_layer :
    (RoutedMatrix.architecture (packetCount vocabulary) (seedLength + front + steps)
      (headCount vocabulary heads locality) (opcodeCount vocabulary heads opcodes locality)).layers = 1 := rfl

theorem fixed_heads :
    (RoutedMatrix.architecture (packetCount vocabulary) (seedLength + front + steps)
      (headCount vocabulary heads locality) (opcodeCount vocabulary heads opcodes locality)).heads =
      heads + (heads + 1) * vocabulary * locality := rfl

/-- PRG security applies to the ciphertext emitted by the actual numerical
Transformer, for every input distribution and predicate. The trace-size
premise is the ordinary polynomial-resource condition required by the PRG
reduction, not a supplied encryption/matrix realization certificate. -/
theorem no_readability
    {inputLength seedLengths fronts times : ℕ → ℕ}
    (schedules : ∀ n, RoutedSchedule.Schedule (fronts n) (times n) heads opcodes)
    (hv : 0 < vocabulary) (plainTransition : Fin opcodes → (Fin heads → Fin vocabulary) → Fin vocabulary)
    (label : Fin vocabulary → Bool) (prompts : ∀ n, Bits (inputLength n) → Fin (fronts n) → Fin vocabulary)
    (generator : NC0GeneratorFamily seedLengths (fun n => times n * vocabulary + vocabulary))
    (secure : generator.IsPseudorandom)
    (monitor : PolynomialMonitorFamily (fun n => times n * vocabulary))
    (coefficient exponent : ℕ) (traceLength : ∀ n, times n * vocabulary ≤ coefficient * (n + 1) ^ exponent) :
    ∃ error : ℕ → ℝ, Negligible error ∧ ∀ n
      (distribution : FiniteDistribution (Bits (inputLength n))) (predicate : Bits (inputLength n) → Bool),
      predictionSuccess distribution
        (fun input seed => transcript (schedules n) hv plainTransition label (generator.generator n) (prompts n input) seed)
        (monitor.monitor n) predicate ≤ distribution.bestConstantSuccess predicate + error n := by
  obtain ⟨error, hnegligible, hprivacy⟩ := PolynomialEncryption.no_readability generator secure
    (fun n input => plainTranscript (schedules n) plainTransition (prompts n input)) monitor coefficient exponent traceLength
  refine ⟨error, hnegligible, ?_⟩
  intro n distribution predicate
  simp_rw [transcript_eq_encryptedTrace]
  exact hprivacy n distribution predicate

end EncryptedMatrix
