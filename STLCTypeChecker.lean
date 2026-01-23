/-
  Topic 14. Simply Typed Lambda Calculus. Decidability of Typing

  Problem:
    Build a type checker for the simplest typed functional language, and prove that the type checker is correct.
    That means it accepts exactly the well-typed programs and rejects exactly the ill-typed ones.

  Solution:
    1. Define types (SimpleType) and terms (Term) → the syntax
    2. Define Context → tracks variables in scope
    3. Define WellTyped → a predicate declaring WHEN a term has a type
    4. Define inferType → an algorithm that COMPUTES a term's type
    5. Prove soundness → if inferType says yes, it's actually well-typed
    6. Prove completeness → if it's well-typed, inferType finds it
    7. Combine into biconditional → the algorithm is correct

  The key insight:
    WellTyped and inferType have the same structure (three cases: var, lam, app).
    The proofs just show they line up perfectly.

  Reference:
    Nederpelt & Geuvers, Type Theory and Formal Proof, Theorem 2.10.10
-/

set_option autoImplicit false


-- Step 1: Basic Definitions

abbrev Var := String
-- ============================================


-- Step 2: Types
/-
  SimpleType represents the types:
    - base: primitive types like "Nat", "Bool"
    - arrow: function types like Nat → Bool

  The ⇒ notation lets us write arrow types nicely:
    SimpleType.base "Nat" ⇒ SimpleType.base "Bool"
  instead of:
    SimpleType.arrow (SimpleType.base "Nat") (SimpleType.base "Bool")

  deriving DecidableEq: lets us compare types with = (needed in inferType)
  deriving Repr: lets us print types with #eval
-/
inductive SimpleType where
  | base : String → SimpleType
  | arrow : SimpleType → SimpleType → SimpleType
  deriving DecidableEq, Repr

namespace SimpleType

infixr:70 " ⇒ " => arrow

#check base "Nat"
#check base "Nat" ⇒ base "Bool"
#check base "Nat" ⇒ base "Nat" ⇒ base "Nat"

end SimpleType
-- ============================================


-- Step 3: Terms
/-
  Term represents lambda calculus expressions:
    - var: a variable like "x"
    - lam: a lambda/function like λx:Nat. body
    - app: function application like f x

  These are the ONLY three constructs in lambda calculus.
  Everything else is built from these.
-/
inductive Term where
  | var : Var → Term
  | lam : Var → SimpleType → Term → Term
  | app : Term → Term → Term
  deriving Repr

namespace Term

-- Examples:
-- λx:Nat. x  (identity function on Nat)
#check lam "x" (SimpleType.base "Nat") (var "x")

-- λf:(Nat→Nat). λx:Nat. f x  (function application)
#check lam "f" (SimpleType.base "Nat" ⇒ SimpleType.base "Nat")
        (lam "x" (SimpleType.base "Nat")
          (app (var "f") (var "x")))

end Term
-- ============================================


-- Step 4: Context (kind of like Valuation in FOL lab example)
/-
  A Context tracks which variables are in scope and their types.
  It's just a list of (variable name, type) pairs.

  empty: start with no variables
  extend: add a variable (used when entering a lambda)
  lookup: find a variable's type (returns Option because it might not exist)

  The two theorems prove that extend and lookup work correctly together:
    - lookup_extend_same: looking up what we just added works
    - lookup_extend_diff: adding y doesn't affect looking up x (when x ≠ y)
-/
def Context := List (Var × SimpleType)

namespace Context

def empty : Context := []

def extend (ctx : Context) (x : Var) (τ : SimpleType) : Context :=
  (x, τ) :: ctx

def lookup (ctx : Context) (x : Var) : Option SimpleType :=
  match ctx with
  | [] => none
  | (y, τ) :: rest => if x = y then some τ else lookup rest x

-- Theorems about lookup like we did for to Valuation.update_same/diff in lab
theorem lookup_extend_same (ctx : Context) (x : Var) (τ : SimpleType) :
    (ctx.extend x τ).lookup x = some τ := by
  simp [extend, lookup]
-- this theorem says that when we extend a context with (x, τ), looking up x gives us τ.

theorem lookup_extend_diff (ctx : Context) (x y : Var) (τ : SimpleType) :
    x ≠ y → (ctx.extend y τ).lookup x = ctx.lookup x := by
  intro h
  simp [extend, lookup, h]
-- this one says that when we extend a context with (y, τ), looking up a variable x gives the same result as before.

end Context
-- ============================================


-- SECTION 5: WellTyped Predicate
/-
  WellTyped is the predicate that declares when a term has a type.

  WellTyped ctx t τ means that in context ctx, term t has type τ

  It's inductive, meaning we define WHEN it's true by listing the three rules.
  If we can't build a proof using these rules, the term is ill-typed.

  It serves as the specification, stating what it means to be well-typed.
-/
inductive WellTyped : Context → Term → SimpleType → Prop where
  | var {ctx : Context} {x : Var} {τ : SimpleType} :
      ctx.lookup x = some τ →
      WellTyped ctx (Term.var x) τ
    /-
      GIVEN ctx, var, type
      IF lookup x = some τ
      THEN is well-typed
    -/

  | lam {ctx : Context} {x : Var} {τ₁ τ₂ : SimpleType} {body : Term} :
      WellTyped (ctx.extend x τ₁) body τ₂ →
      WellTyped ctx (Term.lam x τ₁ body) (SimpleType.arrow τ₁ τ₂)
    /-
      GIVEN ctx, var, input/output, body
      IF body is well-typed with τ₂ (when we add x:τ₁ to context)
      THEN λx:τ₁.body is well-typed with type τ₁ → τ₂
    -/

  | app {ctx : Context} {f a : Term} {τ₁ τ₂ : SimpleType} :
      WellTyped ctx f (SimpleType.arrow τ₁ τ₂) →
      WellTyped ctx a τ₁ →
      WellTyped ctx (Term.app f a) τ₂
    /-
      GIVEN ctx, function f, argument a, types τ₁ and τ₂
      IF f is well-typed with type τ₁ → τ₂
      AND a is well-typed with type τ₁
      THEN f a is well-typed with type τ₂
    -/
-- ============================================


-- SECTION 6: inferType Function
/-
  inferType is the algorithm that computes types.

  Given a context and a term, it returns:
    - some τ if the term has type τ
    - none if the term is ill-typed

  It mirrors WellTyped exactly: same three cases, same logic.
  But while WellTyped declares, inferType computes.

-/
def inferType (ctx : Context) (t : Term) : Option SimpleType :=
  match t with
  | Term.var x => ctx.lookup x
  /-
    For variables: just look up x in context
    If found → some τ, if not found → none
  -/

  | Term.lam x τ body =>
      match inferType (ctx.extend x τ) body with
      | some σ => some (SimpleType.arrow τ σ)
      | none => none
  /-
    For lambdas:
    1. Add x:τ to context
    2. Recursively infer type of body
    IF body has type σ → lambda has type τ → σ
    IF body is ill-typed → lambda is ill-typed
  -/

  | Term.app f a =>
      match inferType ctx f, inferType ctx a with
      | some (SimpleType.arrow τ₁ τ₂), some τ₁' =>
          if τ₁ = τ₁' then some τ₂ else none
      | _, _ => none
  /-
    For applications:
    1. Infer type of f
    2. Infer type of a
    IF f has arrow type τ₁ → τ₂ AND a has type τ₁' THEN
      IF τ₁ = τ₁' (argument matches expected input) → return τ₂
      ELSE → ill-typed (type mismatch)
    ELSE → ill-typed (either f is not a function, or f or a failed)
  -/
-- ============================================


/-
  SECTION 7: Soundness

  If the algorithm says "yes", it's actually correct.
  inferType ctx t = some τ → WellTyped ctx t τ

  1. Assume inferType returned some τ
  2. Induction on the term (var, lam, app)
  3. For each case:
    - Unfold what inferType does for that case
    - Show that if it returned some τ, we can build a WellTyped proof
    - The structure of inferType mirrors WellTyped, so they match up
  4. Impossible branches (where inferType would return none) are contradictions
-/
theorem inferType_sound {ctx : Context} {t : Term} {τ : SimpleType} :
    inferType ctx t = some τ → WellTyped ctx t τ := by
  intro h
  induction t generalizing ctx τ with
  | var x =>
    simp only [inferType] at h
    exact WellTyped.var h
  -- inferType does the lookup, and WellTyped.var needs the lookup

  | lam x τ₁ body ih =>
    simp only [inferType] at h
    split at h
    · case h_1 σ branch1 =>
      injection h with h'
      rw [← h']
      apply WellTyped.lam
      exact ih branch1
    · contradiction
  -- inferType recurses on the lambda's body, and WellTyped.lam needs body to be typed
  -- then use induction hypothesis to connect them

  | app f a ihf iha =>
    simp only [inferType] at h
    split at h
    · rename_i τ₁ τ₂ τ₁' heq_f heq_a
      split at h
      · injection h with h'
        rw [← h']
        apply WellTyped.app
        · exact ihf heq_f
        · rename_i heq_types
          rw [← heq_types] at heq_a
          exact iha heq_a
      · contradiction
    · contradiction
  -- inferType checks that f is of "arrow" type and that a matches. WellTyped.app also needs this
  -- then use induction hypotheses for both f and a
-- ============================================


/-
  SECTION 8: Completeness

  If it's actually well-typed, the algorithm will find it.
  WellTyped ctx t τ → inferType ctx t = some τ

  1. Assume we have a WellTyped proof
  2. Induction on the WellTyped derivation (not the term!)
  3. For each rule (var, lam, app):
    - The WellTyped premises tell us exactly what inferType will compute
    - simp just unfolds and matches everything up
  4. Much easier than soundness because WellTyped gives us all the info we need
-/
theorem inferType_complete {ctx : Context} {t : Term} {τ : SimpleType} :
    WellTyped ctx t τ → inferType ctx t = some τ := by
  intro h
  induction h with
  | var hlookup =>
    simp [inferType, hlookup]
  /-
    hlookup says that ctx.lookup x = some τ
    inferType (Term.var x) does ctx.lookup x
    simp sees they are the same thing
    done
  -/

  | lam _ ih =>
    simp [inferType, ih]
  /-
    ih says that inferType (ctx.extend x τ₁) body = some τ₂
    inferType (Term.lam ...) recurses on body and wraps in arrow
    simp unfolds, uses ih, everything matches
    done
  -/

  | app hf ha ihf iha =>
    simp [inferType, ihf, iha]
  /-
    ihf says that inferType ctx f = some (τ₁ ⇒ τ₂)
    iha says that inferType ctx a = some τ₁
    inferType (Term.app ...) checks both and compares types
    Types match (by construction from WellTyped), so returns some τ₂
    simp handles all of it
    done
  -/
-- ============================================


/-
  SECTION 9: Main Theorem (Biconditional)

  → (completeness): if it's well-typed, algorithm finds it
  ← (soundness): if algorithm finds it, it's well-typed
  ↔ algorithm only accepts exactly the well-typed terms
-/
theorem inferType_correct (ctx : Context) (t : Term) (τ : SimpleType) :
    WellTyped ctx t τ ↔ inferType ctx t = some τ :=
  ⟨inferType_complete, inferType_sound⟩
-- ============================================


/-
  SECTION 10.1: Helper Function to beautify output in infoView
-/
def SimpleType.toString : SimpleType → String
  | .base name => name
  | .arrow τ₁ τ₂ => s!"({τ₁.toString} ⇒ {τ₂.toString})"

def inferTypeStr (ctx : Context) (t : Term) : String :=
  match inferType ctx t with
  | some τ => s!"some {τ.toString}"
  | none => "none"
-- ============================================



/-
  SECTION 10.2: Examples

  Demonstrating the type checker on various terms
-/

/-
  EXAMPLE 1: Identity function

  Term: λx:Nat. x
  A function that takes x of type Nat and returns x

  Type inference:
    1. Enter lambda, add x:Nat to context
    2. Check body (var "x"): lookup "x" → some Nat
    3. Body has type Nat, so lambda has type Nat → Nat

  Result: some (Nat ⇒ Nat) ✓
-/
def idNat : Term := Term.lam "x" (SimpleType.base "Nat") (Term.var "x")
#eval inferTypeStr Context.empty idNat


/-
  EXAMPLE 2: Self-application (ill-typed)

  Term: x x
  "Apply x to itself"

  Type inference:
    1. Look up x in empty context → none
    2. Can't even get types for the subterms

  Result: none ✗
  (Even with x in context, x x is untypeable — would need x : τ → ? and x : τ simultaneously)
-/
def selfApp : Term := Term.app (Term.var "x") (Term.var "x")
#eval inferTypeStr Context.empty selfApp


/-
  EXAMPLE 3: Constant function (curried two-argument function)

  Term: λx:Nat. λy:Bool. x
  "A function that takes x, then y, and returns x (ignoring y)"

  Type inference:
    1. Enter outer lambda, add x:Nat to context
    2. Enter inner lambda, add y:Bool to context
    3. Check body (var "x"): lookup "x" → some Nat
    4. Inner lambda: Bool → Nat
    5. Outer lambda: Nat → (Bool → Nat)

  Result: some (Nat ⇒ (Bool ⇒ Nat)) ✓
  Note: displayed as (Nat ⇒ (Bool ⇒ Nat)) because → is right-associative
-/
def constFn : Term :=
  Term.lam "x" (SimpleType.base "Nat")
    (Term.lam "y" (SimpleType.base "Bool")
      (Term.var "x"))
#eval inferTypeStr Context.empty constFn


/-
  EXAMPLE 4: Function application (higher-order)

  Term: λf:(Nat→Nat). λx:Nat. f x
  "Takes a function f and a value x, applies f to x"

  Type inference:
    1. Enter outer lambda, add f:(Nat→Nat) to context
    2. Enter inner lambda, add x:Nat to context
    3. Check application (f x):
      - f has type Nat → Nat (it's a function!)
      - x has type Nat (matches input!)
      - Result: Nat
    4. Inner lambda: Nat → Nat
    5. Outer lambda: (Nat → Nat) → (Nat → Nat)

  Result: some ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat)) ✓
-/
def applyFn : Term :=
  Term.lam "f" (SimpleType.base "Nat" ⇒ SimpleType.base "Nat")
    (Term.lam "x" (SimpleType.base "Nat")
      (Term.app (Term.var "f") (Term.var "x")))
#eval inferTypeStr Context.empty applyFn


/-
  EXAMPLE 5: Type mismatch (ill-typed)

  Term: λx:Nat. x x
  "Takes x of type Nat, then tries to apply x to x"

  Type inference:
    1. Enter lambda, add x:Nat to context
    2. Check application (x x):
      - x has type Nat
      - Nat is not a function type (not an arrow)!
      - Can't apply a Nat to anything

  Result: none ✗
-/
def badApp : Term :=
  Term.lam "x" (SimpleType.base "Nat")
    (Term.app (Term.var "x") (Term.var "x"))
#eval inferTypeStr Context.empty badApp


/-
  EXAMPLE 6: Context examples

  Term: x
  "Just the variable x"

  With empty context:
    - Look up x → none (x is not in scope!)
    - Result: none ✗

  With context [x : Nat]:
    - Look up x → some Nat
    - Result: some Nat ✓

  Same term, different results depending on what's in scope!
-/
def varInContext : Term := Term.var "x"
#eval inferTypeStr Context.empty varInContext
#eval inferTypeStr (Context.empty.extend "x" (SimpleType.base "Nat")) varInContext
