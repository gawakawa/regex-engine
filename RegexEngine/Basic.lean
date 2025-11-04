/--
Definition of Regular Expressions

r, s ::= ∅     empty set
         ε     empty string
         a     a ∈ Σ
         r · s concatenation
         r*    Kleene-closure
         r | s logical or
         r & s logical and
         ¬r    complement
-/
inductive Regex : Type where
  | emptySet : Regex
  | epsilon : Regex
  | char : Char → Regex
  | concat : Regex → Regex → Regex
  | star : Regex → Regex
  | or : Regex → Regex → Regex
  | and : Regex → Regex → Regex
  | compl : Regex → Regex
  deriving DecidableEq

notation "∅" => Regex.emptySet
notation "ε" => Regex.epsilon
infixl:70 " <> " => Regex.concat
infixl:60 " + " => Regex.or
infixl:65 " & " => Regex.and
postfix:max "*" => Regex.star
prefix:75 "¬" => Regex.compl

/--
Check if a regex accepts the empty string

ν(r) = ε if r is nullable
       ∅ otherwise

ν(ε)     = ε
ν(a)     = ∅
ν(∅)     = ∅
ν(r · s) = ν(r) & ν(s)
ν(r | s) = ν(r) | ν(s)
ν(r*)    = ε
ν(r & s) = ν(r) & ν(s)
ν(¬r)    = ε if ν(r) = ∅
           ∅ if ν(r) = ε
-/
def nullable (r : Regex) : Regex :=
  match r with
  | .epsilon => ε
  | .char _ => ∅
  | .emptySet => ∅
  | .concat r₁ r₂ => nullable r₁ & nullable r₂
  | .or r₁ r₂ => nullable r₁ + nullable r₂
  | .star _ => ε
  | .and r₁ r₂ => nullable r₁ & nullable r₂
  | .compl r' => if nullable r' == ∅ then ε else ∅

/--
Brzozowski Derivative

∂ₐε       = ∅
∂ₐa       = ε
∂ₐb       = ∅ for b ≠ a
∂ₐ∅       = ∅
∂ₐ(r · s) = ∂ₐr · s + ν(r) · ∂ₐs
∂ₐ(r*)    = ∂ₐr · r*
∂ₐ(r | s) = ∂ₐr | ∂ₐs
∂ₐ(r & s) = ∂ₐr & ∂ₐs
∂ₐ(¬r)    = ¬(∂ₐr)
-/
def derivative (c : Char) (r : Regex) : Regex :=
  match r with
  | .epsilon => ∅
  | .char c' => if c == c' then ε else ∅
  | .emptySet => ∅
  | .concat r₁ r₂ => (derivative c r₁ <> r₂) + (nullable r₁ <> derivative c r₂)
  | .star r' => derivative c r' <> r'*
  | .or r₁ r₂ => derivative c r₁ + derivative c r₂
  | .and r₁ r₂ => derivative c r₁ & derivative c r₂
  | .compl r' => ¬(derivative c r')

/--
Check if regex r matches string s

r ∼ ε ↔ ν(r) = ε
r ∼ a · w ↔ ∂ₐr ∼ w
-/
def accept (r : Regex) (s : String) : Bool :=
  nullable (s.foldl (flip derivative) r) == ε
