# Term Former Addition Checklist

This is the complete checklist for adding new term formers to GT3-Lean. Term formers are syntactic constructs that can appear in terms, like variables, applications, abstractions, etc.

## ⚠️ CRITICAL REMINDERS

**Most Common Oversights:**
1. Missing `smul` theorems and their `@[simp]` attributes in Basic.lean
2. Missing cases for `OTm.clamp` and `OTm.fvs` functions in Erase.lean
3. Missing cases for `Tm.bvi` and `OTm.bvi` functions in Erase.lean

**Always double-check these functions - they are easily missed!**

## Overview

Adding a new term former has **two distinct phases** due to GT3-Lean's open-world design:

### Phase 1: Syntax (Optional standalone)
- `Gt3/Syntax/Basic.lean` - Core syntax definitions and operations
- `Gt3/Syntax/Erase.lean` - Erasure to untyped terms

You can add any term former to the syntax without changing typing rules at all. This allows experimenting with new syntax before deciding on typing rules.

### Phase 2: Typing Rules (Optional standalone) 
- `Gt3/JEq/Basic.lean` - Judgmental equality (congruence rule)
- `Gt3/HasTy/Basic.lean` - Typing rules  
- `Gt3/HasTy/Factor.lean` - Inner typing rules

You can also propagate existing JEq rules to HasTy without touching syntax.

**Current constraint**: Term formers use at most one additional binder level (`Tm k` or `Tm (k + 1)`). This may change in future versions.

Tasks may involve:
- **Syntax only**: Add new term former to syntax files only
- **Typing only**: Propagate JEq rules to HasTy files only  
- **Full addition**: Both phases for a complete new term former

## Pre-Implementation Planning

- [ ] Design the syntax: constructor name, parameters, binding structure
- [ ] Plan the typing rule: what type should this term have?
- [ ] Plan the judgmental equality rule: congruence for the new constructor
- [ ] Choose universe levels and constraints

## Implementation Order

### Phase 1: Syntax Files (Can be done standalone)

#### 1. Syntax (`Gt3/Syntax/Basic.lean`)

- [ ] Add constructor to `Tm` inductive type
- [ ] Update `castLE` function
- [ ] Update `open` function  
- [ ] Update `lst` function
- [ ] Update `close` function
- [ ] Update `fvs` function (remember unions for multiple parameters)
- [ ] Update `lsv` function
- [ ] Update `ls` function
- [ ] **CRITICAL**: Write new `smul` theorems for each constructor
- [ ] **CRITICAL**: Add `@[simp]` attributes to the new `smul` theorems
- [ ] Update `depth` function
- [ ] Update `succIndOn` induction principle
- [ ] Update `lcIndCof` induction principle  
- [ ] Update `lcIndFvs` induction principle
- [ ] Add simp lemmas for all operations
- [ ] **IMPORTANT**: After updating `ls`, you must write corresponding `smul` theorems for each new constructor. These define how the `•` operator works: `theorem Tm.smul_pair {...} := rfl`. Then add `@[simp]` attributes to each theorem.
- [ ] Test: `lake build Gt3.Syntax.Basic`

#### 1b. Rewrite Equality (`Gt3/RwEq/Basic.lean`)

- [ ] Add congruence case to `LRwEq` inductive type (for terms at level 0)
- [ ] Add congruence case to `RwEq` inductive type (for terms at any level k)  
- [ ] Include proper binding variable handling in `LRwEq` (use `L : Finset String`)
- [ ] Test: `lake build Gt3.RwEq.Basic`

#### 2. Erasure (`Gt3/Syntax/Erase.lean`)

**Important**: This file contains multiple functions that must ALL be updated. The `bvi` functions are particularly easy to miss since they're defined separately from the main erasure functions.

- [ ] Add constructor to `OTm` inductive type
- [ ] Update `Tm.erase` function
- [ ] **CRITICAL**: Update `OTm.clamp` function (easy to miss!)
- [ ] **CRITICAL**: Update `OTm.fvs` function (easy to miss!)
- [ ] Update `Tm.bvi` function (**CRITICAL**: bound variable index tracking - easy to miss!)
- [ ] Update `OTm.bvi` function
- [ ] Test: `lake build Gt3.Syntax.Erase`

**Stop here if only adding syntax!** The term former now exists syntactically but has no typing rules.

### Phase 2: Typing Files (Can be done standalone)

#### 3. Judgmental Equality (`Gt3/JEq/Basic.lean`)

- [ ] Add congruence rule for the new term former
- [ ] Include proper binding variable handling (use `L : Finset String`)
- [ ] Test: `lake build Gt3.JEq.Basic`

#### 4. Typing Rules (`Gt3/HasTy/Basic.lean`)

- [ ] Add typing rule for the new term former
- [ ] Include universe level constraints
- [ ] Test: `lake build Gt3.HasTy.Basic`

#### 5. Inner Typing (`Gt3/HasTy/Factor.lean`)

- [ ] Mirror the `HasTy` rule in `InnerTy`
- [ ] Ensure parameter names and structure match exactly
- [ ] Test: `lake build Gt3.HasTy.Factor`

## Final Testing

### For Syntax Only:
- [ ] `lake build Gt3.Syntax.Basic`
- [ ] `lake build Gt3.Syntax.Erase`

### For Typing Only:
- [ ] `lake build Gt3.JEq.Basic`  
- [ ] `lake build Gt3.HasTy.Basic`
- [ ] `lake build Gt3.HasTy.Factor`

### For Full Addition:
- [ ] `lake build` (full project build)
- [ ] Check for any remaining errors in dependent files
- [ ] Test with simple examples if possible

## Documentation

- [ ] Update this checklist if new patterns emerge
- [ ] Document any special considerations for this term former
- [ ] Note any files that needed additional changes beyond the core four

## Reduction Rules (Separate Process)

Adding reduction rules to existing term formers is simpler:
- [ ] Add reduction cases to `Gt3/JEq/Basic.lean` only
- [ ] No changes needed to syntax, typing, or factoring files

## Common Gotchas to Check

- [ ] Union order in `fvs` function matches parameter order
- [ ] All `@[simp]` lemmas added for new constructor
- [ ] Binding levels consistent (k vs k+1) across all functions
- [ ] Universe level constraints are consistent and minimal
- [ ] Variable capture avoided in rules with binders
- [ ] Parameter order consistent across all files
- [ ] No missing cases in pattern matches

## Example Parameter Patterns

For reference, common parameter patterns (currently limited to at most one additional binder level):

- **Simple type**: `(A : Tm k)` 
- **Type with binder**: `(A : Tm k) (B : Tm (k + 1))`
- **Term**: `(t : Tm k)`
- **Term with binder**: `(t : Tm (k + 1))`
- **Multiple parameters**: `(A : Tm k) (B : Tm (k + 1)) (b : Tm (k + 1))`

**Current constraint**: No more than one binder level (`k + 1`) is used. Future versions may support `k + 2`, etc.

## Files Usually Needing Updates

### Phase 1 (Syntax):
✅ **Always update these:**
- `Gt3/Syntax/Basic.lean`
- `Gt3/RwEq/Basic.lean` (for `LRwEq` and `RwEq` congruence cases)
- `Gt3/Syntax/Erase.lean`

### Phase 2 (Typing):
✅ **Always update these:**
- `Gt3/JEq/Basic.lean` 
- `Gt3/HasTy/Basic.lean`
- `Gt3/HasTy/Factor.lean`

❓ **Sometimes need updates:**
- Other `HasTy/*.lean` files (if special properties needed)
- Other `JEq/*.lean` files (if special properties needed)

❌ **Rarely need updates:**
- Context files (`Gt3/Ctx.lean`)
- Substitution-specific files (unless new binding patterns)

## Common Mistakes Checklist

Before considering the implementation complete, double-check these frequently missed items:

### Basic.lean:
- [ ] `smul` theorems written for each new constructor
- [ ] `@[simp]` attributes added to new `smul` theorems
- [ ] All major syntax functions updated (especially `fvs`, `lsv`, `ls`)

### Erase.lean: 
- [ ] `OTm.clamp` function updated with new constructor cases
- [ ] `OTm.fvs` function updated with new constructor cases  
- [ ] Both `Tm.bvi` and `OTm.bvi` functions updated

### Build Test:
- [ ] `lake build Gt3.Syntax.Basic` succeeds
- [ ] `lake build Gt3.Syntax.Erase` succeeds

If any of these fail, the missing implementations are likely in the functions listed above.