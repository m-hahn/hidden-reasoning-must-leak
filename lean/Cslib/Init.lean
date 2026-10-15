/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama

SPDX-License-Identifier: Apache-2.0
Adapted from leanprover/cslib, Cslib/Init.lean, revision
311d27ad8458b61e9b7461fc83a480e4be97aef2.
Modified for this project: replace the newer module/public-import syntax and
upstream linter/grind initialization with the pinned Lean/mathlib 4.19 import.
The original author's notice is retained even though the imports are simplified.
See Cslib/LICENSE and NOTICE for the full license and third-party attribution.
-/

import Mathlib

/- The vendored circuit definitions need only Mathlib; upstream initialization
imports newer linter and grind configuration, not mathematical declarations. -/
