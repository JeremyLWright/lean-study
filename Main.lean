import «Study»

#eval 1+1

#eval String.append "Hello " "Dude"

#eval 41 + 19

#eval String.append "A" (String.append "B" "C")

#eval if 3 == 3 then 5 else 7

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


def fac: Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 6


def ack: Nat -> Nat -> Nat
  | 0, n => n + 1
  | m +1, 0=> ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
  termination_by ack m n => (m, n)


inductive State where
  | A | B | C | D | Halt
  deriving Repr

open State

def step : State -> State
  | A => B
  | B => Halt
  | C => D
  | D => C
  | Halt => Halt

def run : Nat -> State -> State
 | 0, s => s
 | n + 1, s => step (run n s)

#eval run 42 A

def A_halts_prop: Prop := 
  exists n: Nat, run n A = Halt 

theorem A_halts : A_halts_prop := by
  exists 2

def C_halts_prop: Prop := 
  ∃ n: Nat, run n C = Halt 

def C_hangs_prop := 
  ¬ ∃ n: Nat, run n C = Halt

def C_hangs_prop2 := 
  ∀ n: Nat, run n C ≠ Halt

theorem C_D_loop:
  ∀ n,
  run n C = C ∨ run n C = D
  := by
  intro n
  induction n with
  | zero => apply Or.inl; rw [run]
  | succ n ih => 
    cases ih with 
    | inl hc => apply Or.inr; rw [run, step, hc]
    | inr hd => apply Or.inl; rw [run, step, hd]

theorem C_hangs: C_hangs_prop2 := by
  intro n
  have is_c_or_d := C_D_loop n
  cases is_c_or_d with
  | inl is_c => rw [is_c]; simp
  | inr is_d => rw [is_d]; simp



