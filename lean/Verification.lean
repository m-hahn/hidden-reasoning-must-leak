import CanonicalArithmetic
import PolynomialEncryption
import TokenSymbolic
import SeededToken
import PhaseSemantics
import PhaseStack
import LeafStep
import EfficientPhase
import EfficientMatrix
import EncryptedEfficientMatrix
import EncryptedSerialization
import MultitapePhase
import TapeProgram
import MultitapeLeaf
import MultitapeMatrix
import EncryptedMultitapeMatrix
import MultiplicationUpper
import ScheduleMatrix
import BinaryObliviousMatrix
import BinaryMultitapeMatrix
import SeedBudget
import PrivatePolynomialTime
import PRGReindex
import CausalToken
import ProtocolToken
import ProtocolMultitapeMatrix
import MultitapeOutputMatrix
import ProtocolSerialization
import ReadoutSchedule
import ScheduleRelabel
import EncryptedReadout
import EncryptedFiniteReadout
import EncryptedMultitapeOutput
import EncryptedMultitapeFiniteOutput
import PrivateOutput
import PrivateWordOutput
import FoldProgram
import ElementaryTaskUpper
import EncryptedFold
import EncryptedTaskUpper
import FiniteProtocolPrivacy
import DelimitedWord
import LogSquaredSeedBudget
import PolylogSeedBudget
import PolylogSourceUpper
import PolylogPrivateBit
import PlainPolylogBit
import ExactPolylogBit
import ExactPolylogTrace
import MultitapeLiteralInitialization
import SchonhageRuntime
import MultiplicationMachineBridge
import SchonhageInitializer
import VerifiedMultiplicationSource
import VerifiedPlainMultiplication
import VerifiedMultiplication
import NearLinearPrivateBit
import PrivateMultiplication
import PolynomialWordOutput
import MultitapeOutputCapacity
import PositiveAdditionFootprint
import ScheduleRecoding
import ExactEncryptedAlphabet
import ExactTaskAlphabet
import CausalSymbolicFootprint
import CausalBoundary
import ExactProtocolToken
import ExactFoldTheorem
import ExactBinaryWord
import PlainBinaryWord
import PlainTasks
import PlainMultiplication
import ExactMultiplication
import FastMultiplication
import NumericalAttention
import NumericalMLP
import CausalMatrix
import CausalMatrixCorrectness
import CausalAutoregressive
import RoutedMatrix
import RoutedMatrixCorrectness
import RoutedAutoregressive
import RoutedLocalMap
import SimulationSizeAudit
import LocalUnrecoverability
import TalRestriction
import TalRandomRestriction
import TalSecondMoment
import TalNumerics
import TalOptimizedNumerics
import TalDecisionTree
import TalSwitching
import TalCommonTree
import TalBlockAdvice
import TalFamilyAdvice
import TalCanonicalCompletion
import TalFamilyWitness
import TalBlockPacking
import TalRecoverableWitness
import TalFamilyDecoding
import TalMultiSwitching
import TalCommonTreeFourier
import TalTreeNormalForm
import TalSignedCircuit
import TalBroadNumerics
import TalSwitchingNumerics
import TalMixedSwitching
import TalShallowCircuit
import TalComplete
import TalConsequences
import Complexitylib
import Lean.Util.CollectAxioms

/-!
# Kernel dependency audit

Building this module fails if a headline result depends on `sorryAx` or on
any nonstandard axiom. Tal is proved locally and audited here. PRG security
remains an explicit argument of encrypted core results. Fast multiplication
remains an argument only of optional older sharp-bound interfaces. The audit includes
the locally verified multiplier, its raw initializer, and the assumption-free
plaintext / PRG-only encrypted replacement headlines, as well as the
complete exact-alphabet task statements, native-prefix information bridges,
raw initializers, and the whole-output compiler.
-/

run_cmd do
  let declarations : Array Lean.Name := #[
    ``TalRandomRestriction.sum_mass,
    ``TalRandomRestriction.expectation_prod,
    ``TalRandomRestriction.coefficient_restricted_character,
    ``TalRandomRestriction.character_cross_moment_zero,
    ``TalRandomRestriction.probability_nonneg,
    ``TalRandomRestriction.probability_le_one,
    ``TalRandomRestriction.coefficient_first_moment,
    ``TalRandomRestriction.coefficient_second_moment,
    ``TalRandomRestriction.probability_aliveSet_eq,
    ``TalRandomRestriction.probability_aliveSet_card,
    ``TalRandomRestriction.tailWeight_transfer,
    ``TalRandomRestriction.tailWeight_binomial_transfer,
    ``TalRandomRestriction.tailWeight_le_expectation_of_binomial_bound,
    ``TalSecondMoment.conditional_cauchy,
    ``TalSecondMoment.probability_ge_half_mean,
    ``TalSecondMoment.second_moment_aliveCount,
    ``TalSecondMoment.binomialTail_ge_eighth,
    ``TalSecondMoment.binomialTail_floor_half_ge_eighth,
    ``TalSecondMoment.tailWeight_le_eight_expectation,
    ``Algebraic.AC0.Switching.card_combinedAdvice_cast_le_ennreal,
    ``Algebraic.AC0.Switching.combinedCanonicalEncoding_injectiveOn_deep,
    ``Algebraic.AC0.RandomRestriction.probability_canonicalDepthAtLeast_combined_scaled_le,
    ``Algebraic.AC0.RandomRestriction.probability_depthAtLeast_restrict_le_five,
    ``Algebraic.AC0.RandomRestriction.probability_cnf_depthAtLeast_restrict_le_five,
    ``TalDecisionTree.slice_tailWeight_eq_zero,
    ``TalDecisionTree.tailWeight_depth_succ,
    ``TalDecisionTree.tailWeight_eq_zero_of_depthAtMost,
    ``TalSwitching.weight_eq_ofReal_mass,
    ``TalSwitching.ofReal_probability,
    ``TalSwitching.expected_tailWeight_le_probability,
    ``TalSwitching.dnf_tailWeight_le,
    ``TalSwitching.cnf_tailWeight_le,
    ``TalCommonTree.hasCommonTree_zero_iff,
    ``TalCommonTree.hasCommonTree_query,
    ``TalCommonTree.exists_bad_transcript,
    ``TalCommonTree.exists_deep_member,
    ``TalCommonTree.hasCommonTree_inputCount,
    ``TalCommonTree.exists_deep_canonical_member,
    ``TalCanonicalCompletion.closedTrace_path,
    ``TalCanonicalCompletion.exists_phase,
    ``TalCanonicalCompletion.Phase.indices_nodup,
    ``TalCanonicalCompletion.Phase.indices_subset_live,
    ``TalBlockAdvice.card_advice_le,
    ``TalFamilyAdvice.family_index_count_le,
    ``TalFamilyAdvice.card_advice_le,
    ``TalFamilyAdvice.card_broadAdvice_le,
    ``TalFamilyWitness.exists_witness,
    ``TalFamilyWitness.Witness.phaseCount_le_slots,
    ``TalFamilyWitness.Witness.indices_nodup_and_subset_live,
    ``TalFamilyWitness.Witness.extension_fixesOnlyLive,
    ``TalFamilyWitness.Witness.extension_fixedCount,
    ``TalFamilyWitness.Witness.clear_extension_recovers,
    ``TalFamilyWitness.Witness.distribution_extension_cross_mul,
    ``TalCanonicalCompletion.exists_boundaryPhase,
    ``TalBlockAdvice.pack,
    ``TalBlockAdvice.Advice.toQueryList_cast,
    ``TalTracePrefix.phase_prefix,
    ``TalFamilyWitness.exists_recoverable_witness,
    ``TalFamilyWitness.Witness.code_answers,
    ``TalFamilyWitness.Witness.code_members_expand,
    ``TalFamilyWitness.Witness.code_blocks,
    ``TalPhaseSplit.boundaryPhase_split,
    ``TalPhaseSplit.splitPhase_clearLastClose,
    ``TalFutureReplay.closedTrace_replay_future,
    ``TalFamilyFrames.replay_phase,
    ``TalFamilyFrames.reset_phase,
    ``TalFamilyWitness.Witness.queryAdvice_eq_packed,
    ``TalFamilyDecoding.run_witness,
    ``TalFamilyDecoding.decode_encode,
    ``TalMultiSwitching.encode_injectiveOn_bad,
    ``TalMultiSwitching.probability_bad_card_scaled_le,
    ``TalMultiSwitching.probability_bad_scaled_le,
    ``TalMultiSwitching.probability_bad_le,
    ``TalMultiSwitching.real_probability_bad_le,
    ``TalMultiSwitching.real_probability_bad_le_geometric,
    ``TalCommonTreeFourier.tailWeight_eq_slice_of_slices_eq,
    ``TalCommonTreeFourier.tailWeight_fixed_eq_slice,
    ``TalCommonTreeFourier.tailWeight_query,
    ``TalCommonTree.Tree.tailWeight_bound,
    ``TalCommonTree.Tree.tailWeight_bound_of_depth_le,
    ``TalTreeNormalForm.addLiteral_satisfied,
    ``TalTreeNormalForm.addLiteral_width,
    ``TalTreeNormalForm.toDNF_eval,
    ``TalTreeNormalForm.toDNF_width,
    ``TalTreeNormalForm.toCNF_eval,
    ``TalTreeNormalForm.toCNF_width,
    ``TalTreeNormalForm.normalForms_of_depthAtMost,
    ``TalSignedCircuit.compile_eval,
    ``TalSignedCircuit.compile_depth_le,
    ``TalSignedCircuit.compile_gateCount_le,
    ``TalSignedCircuit.exists_routing_of_depth_zero,
    ``TalSignedCircuit.literal_tailWeight_eq_zero,
    ``TalSignedCircuit.zero_depth_tailBound,
    ``TalBroadNumerics.constant_bound,
    ``TalBroadNumerics.denominator_bound,
    ``TalBroadNumerics.raw_bound_to_tailBound,
    ``TalSwitchingNumerics.parameter_small,
    ``TalSwitchingNumerics.geometric_pow_le,
    ``TalSwitchingNumerics.geometric_floor_le,
    ``TalSwitchingNumerics.probability_bad_le_raw,
    ``TalSwitchingNumerics.probability_bad_le,
    ``TalSwitchingNumerics.retained_degree_bound,
    ``TalMixedSwitching.leafBound_signedFamily_iff,
    ``TalMixedSwitching.hasCommonTree_signedFamily_iff,
    ``TalMixedSwitching.hasCommonTree_dnfView_iff,
    ``TalMixedSwitching.probability_no_commonTree_le,
    ``TalMixedSwitching.NormalForm.eval_negate,
    ``TalMixedSwitching.NormalForm.WidthAtMost.negate,
    ``TalShallowCircuit.singleton_eval,
    ``TalShallowCircuit.orLiterals_eval,
    ``TalShallowCircuit.orLiterals_width,
    ``TalShallowCircuit.andLiterals_eval,
    ``TalShallowCircuit.andLiterals_width,
    ``TalShallowCircuit.normalForm_of_depth_le_one,
    ``TalShallowCircuit.shallow_tailBound,
    ``TalShallowCircuit.tailWeight_le_of_depth_le_one,
    ``TalGateNetwork.normalForm_of_shallow_inputs,
    ``TalGateNetwork.Model.lower,
    ``TalGateNetwork.Model.reindex,
    ``TalGateNetwork.Model.pad,
    ``TalSharedCircuit.Graph.toModel,
    ``TalSharedCircuit.card_gateType,
    ``TalSharedCircuit.realize_eval,
    ``TalSharedCircuit.realize_bound,
    ``TalSharedCircuit.exists_model,
    ``TalGateNetwork.Model.bottom_depth_of_family,
    ``TalNetworkFourier.good_bound,
    ``TalNetworkFourier.bad_bound,
    ``TalNetworkFourier.raw_tail_bound,
    ``TalComplete.fourierTailTheorem,
    ``TalConsequences.parityCorrelation_sq_le,
    ``TalConsequences.circuit_correlation_le,
    ``TalConsequences.footprint,
    ``TalConsequences.multiplication_footprint,
    ``TalConsequences.multiplication_length,
    ``TalRestriction.uniformExpectation_split,
    ``TalRestriction.coefficient_liftSet,
    ``TalRestriction.coefficient_insert_liftSet,
    ``TalRestriction.coefficient_energy_split,
    ``TalRestriction.coefficient_eq_zero_of_slices_eq,
    ``TalRestriction.coefficient_const,
    ``TalRestriction.tailWeight_const,
    ``TalRestriction.tailWeight_le_one_of_sign,
    ``TalRestriction.average_slice_tailWeight,
    ``TalRestriction.random_coordinate_tailWeight,
    ``TalRestriction.tailWeight_slice,
    ``TalRestriction.RestrictionTree.tailWeight_bound,
    ``TalRestriction.RestrictionTree.tailWeight_bound_of_depth_le,
    ``TalRestriction.DecisionTree.tailWeight_depth_succ,
    ``TalRestriction.DecisionTree.coefficient_eq_zero_of_depth_lt,
    ``TalNumerics.absorb_prefactor,
    ``TalNumerics.constant_bound,
    ``TalNumerics.logb_double_size_le,
    ``TalNumerics.denominator_bound,
    ``TalNumerics.raw_bound_to_tailBound,
    ``TalOptimizedNumerics.constant_bound,
    ``TalOptimizedNumerics.eight_half_pow_floor_le,
    ``TalOptimizedNumerics.logb_seventeen_le,
    ``TalOptimizedNumerics.prefactor_bound,
    ``TalOptimizedNumerics.denominator_bound,
    ``TalOptimizedNumerics.raw_bound_to_tailBound,
    ``PolylogSeedBudget.capacity,
    ``PolylogSeedBudget.sublinear,
    ``PolylogSeedBudget.inverse_bound,
    ``PolylogSourceUpper.source_polynomial,
    ``PolylogSourceUpper.trace_bound,
    ``PolylogPrivateBit.generatorPrefix_secure,
    ``PolylogPrivateBit.generated_output,
    ``PolylogPrivateBit.no_readability,
    ``PlainPolylogBit.generated_output,
    ``PlainPolylogBit.context_bound,
    ``PlainPolylogBit.polynomial_resources,
    ``PlainPolylogBit.architecture_fixed,
    ``ExactPolylogBit.architecture_fixed,
    ``ExactPolylogBit.generated_output,
    ``ExactPolylogBit.context_bound,
    ``ExactPolylogBit.polynomial_resources,
    ``ExactPolylogTrace.answer_correct,
    ``ExactPolylogTrace.multiplication_footprint,
    ``MultitapeLiteralInitialization.binaryLiteral_correct,
    ``SchonhageRuntime.time_bound,
    ``MultiplicationMachineBridge.run_corresponds,
    ``MultiplicationMachineBridge.padded_run,
    ``SchonhageInitializer.sources_correct,
    ``SchonhageInitializer.left_value,
    ``SchonhageInitializer.right_value,
    ``VerifiedMultiplicationSource.time_bound,
    ``VerifiedMultiplicationSource.full_product,
    ``VerifiedMultiplicationSource.middle_bit,
    ``VerifiedPlainMultiplication.complete,
    ``VerifiedMultiplication.output_correct,
    ``VerifiedMultiplication.privacy,
    ``VerifiedMultiplication.resources,
    ``VerifiedMultiplication.complete,
    ``MultitapeTuring.Machine.tape_eq_initial_above,
    ``MultitapeOutputCapacity.word_length,
    ``MultitapeOutputCapacity.capacity_polynomial,
    ``PolynomialWordOutput.word_correct,
    ``PolynomialWordOutput.no_readability,
    ``PolynomialWordOutput.polynomial_resources,
    ``TokenSymbolic.positive_addition100_uniform_expected_length,
    ``NearLinearPrivateBit.payload_bound,
    ``NearLinearPrivateBit.capacity,
    ``NearLinearPrivateBit.generatorPrefix_secure,
    ``NearLinearPrivateBit.generated_output,
    ``NearLinearPrivateBit.context_bound,
    ``NearLinearPrivateBit.no_readability,
    ``NearLinearPrivateBit.precision_fixed,
    ``NearLinearPrivateBit.polynomial_resources,
    ``PrivateMultiplication.encrypted_upper_bound,
    ``LogSquaredSeedBudget.log_squared_bound,
    ``LogSquaredSeedBudget.capacity,
    ``LogSquaredSeedBudget.sublinear,
    ``LogSquaredSeedBudget.inverse_bound,
    ``PolynomialEncryption.pointwise_security_finite,
    ``PolynomialEncryption.no_readability_finite,
    ``ReadoutSchedule.prefix_correct,
    ``ReadoutSchedule.read_correct,
    ``RoutedSchedule.token_lift,
    ``EncryptedReadout.output_correct,
    ``EncryptedReadout.no_readability,
    ``EncryptedFiniteReadout.output_correct,
    ``EncryptedFiniteReadout.no_readability_finite,
    ``EncryptedFiniteReadout.inputLiteral_correct,
    ``EncryptedFiniteReadout.polynomial_resources,
    ``EncryptedMultitapeOutput.generated_output,
    ``EncryptedMultitapeOutput.inputCircuit_correct,
    ``EncryptedMultitapeOutput.inputCircuit_depth,
    ``EncryptedMultitapeFiniteOutput.generated_output,
    ``EncryptedMultitapeFiniteOutput.whole_word_correct,
    ``EncryptedMultitapeFiniteOutput.inputCircuit_correct,
    ``EncryptedMultitapeFiniteOutput.inputCircuit_depth,
    ``PrivateOutput.output_at_source_time,
    ``PrivateOutput.no_readability,
    ``PrivateOutput.context_bound,
    ``PrivateOutput.polynomial_resources,
    ``PrivateWordOutput.word_correct,
    ``PrivateWordOutput.no_readability,
    ``PrivateWordOutput.polynomial_resources,
    ``FoldProgram.control_final,
    ``FoldProgram.generated_result,
    ``ElementaryTaskUpper.parity_correct,
    ``ElementaryTaskUpper.s5_full_product_correct,
    ``ElementaryTaskUpper.addition_correct,
    ``EncryptedFold.generated_output,
    ``EncryptedFold.generatorPrefix_secure,
    ``EncryptedFold.no_readability,
    ``EncryptedFold.context_linear,
    ``EncryptedFold.seed_sublinear,
    ``EncryptedTaskUpper.parity_correct,
    ``EncryptedTaskUpper.s5_full_product_correct,
    ``EncryptedTaskUpper.addition_correct,
    ``EncryptedTaskUpper.eos_generated,
    ``EncryptedTaskUpper.polynomial_resources,
    ``DelimitedWord.decode_getElem,
    ``DelimitedWord.first_eos,
    ``SeedBudget.seed_inverse_bound,
    ``PRGReindex.negligible_reindex,
    ``PRGReindex.secure,
    ``PrivatePolynomialTime.chosenGenerator_secure,
    ``PrivatePolynomialTime.no_readability,
    ``PrivatePolynomialTime.no_readability_full_word,
    ``PrivatePolynomialTime.output_at_source_time,
    ``PrivatePolynomialTime.context_bound,
    ``CausalMatrix.gateCost_monotone,
    ``CausalToken.generated_correct,
    ``CausalToken.fixed_length,
    ``CausalToken.fixed_answer,
    ``ProtocolMatrix.token_correct,
    ``ProtocolMatrix.separator_generated,
    ``ProtocolMatrix.output_suffix_correct,
    ``ProtocolEncryptedBinary.payload_correct,
    ``ProtocolEncryptedBinary.separator_generated,
    ``ProtocolEncryptedBinary.output_correct,
    ``ProtocolEncryptedBinary.inputLiteral_correct,
    ``ProtocolEncryptedBinary.no_readability,
    ``ProtocolToken.answer_correct,
    ``ProtocolToken.length_fixed,
    ``ProtocolToken.parity_leakage,
    ``ProtocolMultitapeMatrix.output_correct,
    ``ProtocolMultitapeMatrix.inputLiteral_correct,
    ``ProtocolMultitapeMatrix.inputCircuit_depth,
    ``ProtocolMultitapeMatrix.no_readability,
    ``ProtocolMultitapeMatrix.one_layer,
    ``ProtocolMultitapeMatrix.heads_fixed,
    ``ProtocolMultitapeMatrix.precision_fixed,
    ``ProtocolMultitapeMatrix.tokenModel_answer,
    ``ProtocolMultitapeMatrix.parity_leakage,
    ``MultitapeOutputMatrix.output_cell_correct,
    ``MultitapeOutputMatrix.generated_output,
    ``ProtocolSerialization.eval_encodingCircuit,
    ``ProtocolSerialization.encodingCircuit_depth,
    ``ProtocolSerialization.encodingCircuit_size,
    ``ProtocolSerialization.transcript_eq_encode,
    ``ProtocolSerialization.no_readability,
    ``CanonicalArithmetic.matrix_transformer_to_ac0,
    ``TransformerAC0.FixedPrecisionTransformer.run_eq_label_runToken,
    ``FiniteInformation.Distribution.entropy_tradeoff,
    ``FiniteInformation.Distribution.private_randomness_information_lower_bound,
    ``FiniteInformation.TerminatedCode.entropy_le_expected_terminated_length,
    ``TokenAutoregressive.Generator.eval_fiberCircuit,
    ``TokenAutoregressive.Generator.expected_length_lower_bound,
    ``TokenAutoregressive.Generator.seeded_footprint,
    ``TokenAutoregressive.Generator.seeded_expected_length_lower_bound,
    ``TokenAutoregressive.Generator.seeded_public_length_tax,
    ``TokenAutoregressive.Generator.seeded_multiplication_footprint,
    ``TokenAutoregressive.Generator.seeded_multiplication_expected_length_lower_bound,
    ``ConcreteReasoning.token_hidden_reasoning_tax,
    ``ConcreteReasoning.token_multiplication_expected_length,
    ``TokenSymbolic.s5_uniform_expected_length,
    ``TokenSymbolic.addition100_uniform_expected_length,
    ``PolynomialEncryption.leakage_and_privacy,
    ``ObliviousProgram.Program.compile_output,
    ``ObliviousProgram.constantWidthCode,
    ``ObliviousPhase.Machine.run_rotate,
    ``ObliviousPhase.Machine.phaseExecution_correct,
    ``ObliviousPhase.horizon_linear_work_bound,
    ``ObliviousCopy.program_complete,
    ``ObliviousCopy.scan_destination,
    ``RotationProgram.rotate_main,
    ``RotationProgram.rotate_length,
    ``HeadMarker.detect_correct,
    ``CompressedTape.compress_represents,
    ``PhaseStack.compressSaved_represents,
    ``PhaseStack.compressSaved_choice,
    ``PhaseStack.expand_represents,
    ``LeafStep.step_correct,
    ``LeafStep.instruction_count,
    ``LeafStep.token_alphabet_card,
    ``EfficientPhase.source_run_correct,
    ``EfficientPhase.instruction_count,
    ``EfficientPhase.horizon_instruction_count,
    ``EfficientPhase.program_correct,
    ``EfficientPhase.two_head_output,
    ``EfficientPhase.padded_program_correct,
    ``EfficientPhase.bitProgram_correct,
    ``ObliviousMatrix.generated_correct,
    ``ObliviousMatrix.output_correct,
    ``ObliviousMatrix.parameter_count_bound,
    ``EfficientMatrix.matrix_output,
    ``EfficientMatrix.padded_matrix_output,
    ``EfficientMatrix.generated_count_bound,
    ``EfficientMatrix.inputEncoding_literal,
    ``EfficientMatrix.inputCircuit_correct,
    ``EfficientMatrix.inputCircuit_depth,
    ``EfficientMatrix.vocabulary_fixed,
    ``EfficientMatrix.matrix_precision_fixed,
    ``EfficientMatrix.dimension_polynomial_bound,
    ``EfficientMatrix.parameter_polynomial_bound,
    ``Encryption.LocalGenerator.truthTable_correct,
    ``RoutedSchedule.token_ofPlan,
    ``EncryptedMatrix.generated_correct,
    ``EncryptedMatrix.output_correct,
    ``EncryptedMatrix.transcript_eq_encryptedTrace,
    ``EncryptedMatrix.full_transcript_reconstructible,
    ``EncryptedMatrix.no_readability,
    ``EncryptedMatrix.fixed_precision,
    ``EncryptedObliviousMatrix.token_correct,
    ``EncryptedObliviousMatrix.output_correct,
    ``EncryptedObliviousMatrix.transcript_eq_encryptedTrace,
    ``EncryptedObliviousMatrix.no_readability,
    ``EncryptedEfficientMatrix.matrix_output,
    ``EncryptedEfficientMatrix.padded_matrix_output,
    ``EncryptedEfficientMatrix.inputEncoding_literal,
    ``EncryptedEfficientMatrix.inputCircuit_correct,
    ``EncryptedEfficientMatrix.inputCircuit_depth,
    ``EncryptedEfficientMatrix.inputCircuit_size,
    ``EncryptedEfficientMatrix.matrix_precision_fixed,
    ``EncryptedEfficientMatrix.generated_count_bound,
    ``EncryptedEfficientMatrix.ciphertext_count_bound,
    ``EncryptedEfficientMatrix.no_readability,
    ``EncryptedEfficientMatrix.dimension_polynomial_bound,
    ``EncryptedEfficientMatrix.parameter_polynomial_bound,
    ``EncryptedSerialization.eval_encodingCircuit,
    ``EncryptedSerialization.encodingCircuit_depth,
    ``EncryptedSerialization.encodingCircuit_size,
    ``EncryptedSerialization.transcript_eq_encode,
    ``EncryptedSerialization.no_readability,
    ``MultitapeTuring.Machine.head_distance_le,
    ``MultitapeTuring.Machine.step_permute,
    ``MultitapeTuring.Machine.run_rotate,
    ``MultitapeTuring.Machine.terminal_run_after,
    ``MultitapeTuring.Machine.phaseExecution_correct,
    ``TapeProgram.run_project,
    ``TapeProgram.run_other,
    ``MultitapeCompression.compress_represents,
    ``MultitapeCompression.compressSaved_represents,
    ``MultitapeCompression.compressSaved_choice,
    ``MultitapeCompression.expand_represents,
    ``MultitapeLeaf.readTapes_correct,
    ``MultitapeLeaf.step_correct,
    ``MultitapeLeaf.instruction_count,
    ``MultitapeLeaf.registers_card,
    ``MultitapeLeaf.instructions_buffer,
    ``MultitapeBatches.compression_correct,
    ``MultitapeBatches.compression_choices,
    ``MultitapeBatches.expansion_correct,
    ``MultitapeBatches.compression_preserves_slot,
    ``MultitapeBatches.expansion_preserves_slot,
    ``MultitapeEfficientPhase.preserves_earlier_slot,
    ``MultitapeEfficientPhase.phase_represents,
    ``MultitapeEfficientPhase.source_run_correct,
    ``MultitapeEfficientPhase.instruction_count,
    ``MultitapeEfficientPhase.horizon_instruction_count,
    ``MultitapeEfficientPhase.program_correct,
    ``MultitapeMatrix.output_correct,
    ``MultitapeMatrix.bit_output_correct,
    ``MultitapeMatrix.inputLiteral_correct,
    ``MultitapeMatrix.inputCircuit_correct,
    ``MultitapeMatrix.inputCircuit_depth,
    ``MultitapeMatrix.precision_fixed,
    ``MultitapeMatrix.transcript_count_bound,
    ``MultitapeMatrix.event_polynomial_bound,
    ``MultitapeMatrix.polynomial_log_trace_bound,
    ``EncryptedMultitapeMatrix.output_correct,
    ``EncryptedMultitapeMatrix.inputLiteral_correct,
    ``EncryptedMultitapeMatrix.inputCircuit_correct,
    ``EncryptedMultitapeMatrix.inputCircuit_depth,
    ``EncryptedMultitapeMatrix.no_readability,
    ``EncryptedMultitapeMatrix.precision_fixed,
    ``MultiplicationUpper.trace_bound,
    ``MultiplicationUpper.dimension_polynomial_bound,
    ``MultiplicationUpper.parameter_polynomial_bound,
    ``MultiplicationUpper.matrix_upper_bound,
    ``RoutedSchedule.generated_correct,
    ``RoutedSchedule.output_correct,
    ``BinarySchedule.read_word,
    ``BinarySchedule.step_correct,
    ``BinarySchedule.token_correct,
    ``BinaryMatrix.generated_correct,
    ``BinaryMatrix.output_correct,
    ``BinaryMatrix.inputLiteral_correct,
    ``BinaryMatrix.inputCircuit_correct,
    ``BinaryMatrix.inputCircuit_depth,
    ``BinaryMatrix.precision_fixed,
    ``EncryptedBinaryMatrix.repeat_pad,
    ``EncryptedBinaryMatrix.binaryPacket_injective,
    ``EncryptedBinaryMatrix.generated_binary,
    ``EncryptedBinaryMatrix.transcript_eq_encryptedTrace,
    ``EncryptedBinaryMatrix.output_correct,
    ``EncryptedBinaryMatrix.no_readability,
    ``BinaryObliviousMatrix.output_correct,
    ``BinaryObliviousMatrix.encrypted_output_correct,
    ``BinaryObliviousMatrix.encrypted_binary,
    ``BinaryMultitapeMatrix.output_correct,
    ``BinaryMultitapeMatrix.encrypted_output_correct,
    ``BinaryMultitapeMatrix.inputCircuit_correct,
    ``BinaryMultitapeMatrix.inputCircuit_depth,
    ``BinaryMultitapeMatrix.binary_count_bound,
    ``BinaryMultitapeMatrix.no_readability,
    ``SeedBudget.exponent_bounds,
    ``SeedBudget.slack_positive,
    ``SeedBudget.logarithm_bound,
    ``SeedBudget.stretch_capacity,
    ``SeedBudget.seed_power_bound,
    ``SeedBudget.seed_polynomial_bound,
    ``SeedBudget.stretch_floor_capacity,
    ``SeedBudget.sublinear_seed_and_capacity,
    ``PRGRestriction.uniformAcceptance_restrict,
    ``PRGRestriction.advantage_restrict,
    ``PRGRestriction.secure,
    ``PrivatePolynomialTime.payload_bound,
    ``PrivatePolynomialTime.capacity,
    ``PrivatePolynomialTime.generatorPrefix_secure,
    ``PrivatePolynomialTime.seed_resource_bounds,
    ``FastMultiplication.middleBit_eq,
    ``FastMultiplication.initialTape_raw,
    ``FastMultiplication.time_polynomial,
    ``FastMultiplication.padded_full_product,
    ``NumericalPrimitives.aggregate_eq_matrix_aggregate,
    ``NumericalPrimitives.exponentiate_negative_one,
    ``NumericalAttention.dotScore_exact,
    ``NumericalAttention.output_exact,
    ``NumericalAttention.two_bit_output_exact,
    ``NumericalMLP.fixed_grid_output,
    ``CausalMatrix.learned_weights_shared,
    ``CausalMatrix.prefix_compile_depth,
    ``CausalMatrix.hidden_agrees,
    ``CausalMatrix.chosenToken_agrees,
    ``CausalAutoregressive.Model.eval_predictionCircuit,
    ``CausalAutoregressive.Model.predictionCircuit_depth,
    ``CausalAutoregressive.Model.predictionCircuit_polynomial_size,
    ``RoutedMatrix.hidden_dimension_linear,
    ``RoutedMatrix.parameter_count_quadratic,
    ``RoutedMatrix.tokenScalarValue_oneHot,
    ``RoutedMatrix.run_token_correct,
    ``RoutedMatrix.run_correct,
    ``RoutedMatrix.run_token_prefix_correct,
    ``RoutedMatrix.prefix_input_literal,
    ``RoutedMatrix.autoregressive_correct,
    ``RoutedMatrix.answer_correct,
    ``RoutedMatrix.transitionMap_features,
    ``RoutedMatrix.transition_prefix_correct,
    ``SimulationSizeAudit.configurationToken_code_width_lower_bound,
    ``LocalUnrecoverability.canonicalSymmetricTrace_information,
    ``LocalUnrecoverability.canonicalSymmetricTrace_no_bit_recoverable,
    ``LocalUnrecoverability.canonicalSymmetricTrace_output,
    ``ScheduleRecoding.token_correct,
    ``ReadoutSchedule.source_before_readouts,
    ``ExactEncryptedAlphabet.source_recovery,
    ``ExactEncryptedAlphabet.token_correct,
    ``ExactEncryptedAlphabet.generated_correct,
    ``ExactEncryptedAlphabet.payload_correct,
    ``ExactEncryptedAlphabet.output_correct,
    ``ExactEncryptedAlphabet.inputLiteral_correct,
    ``ExactEncryptedAlphabet.no_readability_finite,
    ``ExactEncryptedAlphabet.precision_fixed,
    ``ExactEncryptedAlphabet.polynomial_resources,
    ``ExactTaskAlphabet.s5_vocabulary_card,
    ``ExactTaskAlphabet.decodeBinaryToken_output,
    ``CausalSymbolicToken.generated_correct,
    ``CausalSymbolicToken.length_eq,
    ``CausalSymbolicToken.answer_eq,
    ``CausalSymbolicToken.entropy_prefix,
    ``CausalBoundary.length_eq,
    ``CausalBoundary.answer_eq,
    ``ExactProtocolToken.length_fixed,
    ``ExactProtocolToken.native_answer,
    ``ExactProtocolToken.native_trace,
    ``ExactFold.generated_output,
    ``ExactFold.polynomial_resources,
    ``ExactFoldPrompt.prompt_correct,
    ``CausalSymbolicToken.recoverPrefix_correct,
    ``ExactFoldTrace.trace_native,
    ``ExactFoldTrace.information_lower_bound,
    ``ExactFoldTrace.expected_length_lower_bound,
    ``ExactTasks.parity_output,
    ``ExactTasks.s5_output,
    ``ExactTasks.addition_output,
    ``ExactTasks.parity_footprint,
    ``ExactTasks.s5_footprint,
    ``ExactTasks.addition_footprint,
    ``ExactFoldTheorem.complete,
    ``ExactTasks.elementary_tasks_complete,
    ``ExactMultitapeOutput.generated_output,
    ``ExactMultitapeOutput.inputCircuit_correct,
    ``ExactMultitapeOutput.inputCircuit_depth,
    ``ExactBinaryWord.whole_function_correct,
    ``ExactBinaryWord.architecture_fixed,
    ``ExactBinaryWord.context_bound,
    ``ExactBinaryWord.polynomial_resources,
    ``ExactBinaryWord.no_readability,
    ``PlainBinaryWord.whole_function_correct,
    ``PlainBinaryWord.architecture_fixed,
    ``PlainBinaryWord.context_bound,
    ``PlainBinaryWord.polynomial_resources,
    ``PlainTasks.parity_output,
    ``PlainTasks.s5_output,
    ``PlainTasks.addition_output,
    ``PlainTasks.context_linear,
    ``PlainTasks.architecture_fixed,
    ``PlainTasks.polynomial_resources,
    ``PlainMultiplication.generated_output,
    ``PlainMultiplication.context_bound,
    ``PlainMultiplication.architecture_fixed,
    ``PlainMultiplication.complete,
    ``ExactNearLinear.generated_output,
    ``ExactNearLinear.context_bound,
    ``ExactNearLinear.no_readability,
    ``ExactNearLinear.polynomial_resources,
    ``ExactNearLinearTrace.answer_correct,
    ``ExactNearLinearTrace.multiplication_footprint,
    ``ExactMultiplication.source_exists,
    ``ExactMultiplication.privacy,
    ``ExactMultiplication.resources,
    ``ExactMultiplication.complete]
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let environment ← Lean.getEnv
  -- Traverse shared proof dependencies only once across the entire audit.
  -- This is the standard collector's state, not a cache of trusted results.
  let mut auditState : Lean.CollectAxioms.State := {}
  for declaration in declarations do
    unless environment.contains declaration do
      throwError "Audited declaration is missing: {declaration}"
    let (_, nextState) :=
      ((Lean.CollectAxioms.collect declaration).run environment).run auditState
    auditState := nextState
    for axiomName in auditState.axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
