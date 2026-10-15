/- Ported to the faithfulness project's pinned Lean/mathlib v4.19.0.
Upstream revision add0aca8ee0d71e68969f2cb45cf91554a50f787; original copyright/license below. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Signature

/-!
# Circuit signatures from CSLib

The library uses CSLib's finite-arity signatures directly. This re-export
preserves the `Algebraic.Signature` name without introducing a second model.
-/
namespace Algebraic

export Cslib.Circuits (Signature)

end Algebraic
