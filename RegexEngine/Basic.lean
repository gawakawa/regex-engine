inductive Regex : Type where
  | epsilon : Regex
  | char : Char → Regex
  | concat : Regex → Regex → Regex
  | star : Regex → Regex

def nullable : Regex → Bool := sorry

def derivative (c : Char) : Regex → Regex := sorry

def accept (r : Regex) (s : String) : Bool := sorry
