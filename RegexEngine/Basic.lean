/--
Definition of Regular Expressions

r, s ::= ∅     empty set
         ε     empty string
         a     a ∈ Σ
         r · s concatenation
         r*    Kleene-closure
         r + s logical or
         r & s logical and
         ¬ r   complement
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

notation "∅" => Regex.emptySet
notation "ε" => Regex.epsilon
infixl:70 " · " => Regex.concat
infixl:60 " + " => Regex.or
infixl:65 " & " => Regex.and
postfix:max "*" => Regex.star
prefix:75 "¬" => Regex.compl

def nullable : Regex → Bool := sorry

def derivative (c : Char) : Regex → Regex := sorry

def accept (r : Regex) (s : String) : Bool := sorry
