import RegexEngine

def main : IO Unit :=
  let r := (Regex.char 'a') <> (Regex.char 'b')
  IO.println s!"{accept r "ab"}"
