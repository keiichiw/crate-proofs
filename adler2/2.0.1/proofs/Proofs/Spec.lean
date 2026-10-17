module
public import Adler2

@[expose] public section

open Aeneas.Std

namespace adler2

def modulus : Nat := 65521

def normalize (s : Nat × Nat) : Nat × Nat :=
  (s.1 % modulus, s.2 % modulus)

def step (s : Nat × Nat) (byte : U8) : Nat × Nat :=
  let a := (s.1 + byte.val) % modulus
  (a, (s.2 + a) % modulus)

def run (s : Nat × Nat) (bytes : List U8) : Nat × Nat :=
  bytes.foldl step (normalize s)

def observe (s : Adler32) : Nat × Nat := (s.a.val, s.b.val)

def encode (s : Nat × Nat) : Nat := s.2 * 65536 + s.1

theorem modulus_pos : 0 < modulus := by decide

theorem normalize_normalized (s : Nat × Nat) :
    (normalize s).1 < modulus ∧ (normalize s).2 < modulus := by
  simp only [normalize]
  exact ⟨Nat.mod_lt _ modulus_pos, Nat.mod_lt _ modulus_pos⟩

theorem normalize_idempotent (s : Nat × Nat) :
    normalize (normalize s) = normalize s := by
  simp [normalize]

theorem step_normalized (s : Nat × Nat) (byte : U8) :
    (step s byte).1 < modulus ∧ (step s byte).2 < modulus := by
  simp only [step]
  exact ⟨Nat.mod_lt _ modulus_pos, Nat.mod_lt _ modulus_pos⟩

theorem normalize_step (s : Nat × Nat) (byte : U8) :
    normalize (step s byte) = step s byte := by
  simp [normalize, step]

theorem run_normalized (s : Nat × Nat) (bytes : List U8) :
    (run s bytes).1 < modulus ∧ (run s bytes).2 < modulus := by
  induction bytes generalizing s with
  | nil => exact normalize_normalized s
  | cons byte rest ih =>
      simp only [run, List.foldl_cons]
      have h : (rest.foldl step (step (normalize s) byte)) =
          run (step (normalize s) byte) rest := by
        simp [run, normalize_step]
      rw [h]
      exact ih _

theorem normalize_of_bounds (s : Nat × Nat)
    (ha : s.1 < modulus) (hb : s.2 < modulus) :
    normalize s = s := by
  cases s with
  | mk a b => simp [normalize, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem normalize_run (s : Nat × Nat) (bytes : List U8) :
    normalize (run s bytes) = run s bytes := by
  obtain ⟨ha, hb⟩ := run_normalized s bytes
  exact normalize_of_bounds _ ha hb

theorem run_normalize_seed (s : Nat × Nat) (bytes : List U8) :
    run (normalize s) bytes = run s bytes := by
  simp only [run, normalize_idempotent]

theorem run_of_mod_eq (s t : Nat × Nat) (bytes : List U8)
    (ha : s.1 % modulus = t.1 % modulus)
    (hb : s.2 % modulus = t.2 % modulus) :
    run s bytes = run t bytes := by
  have hnorm : normalize s = normalize t := by
    simpa only [normalize, Prod.mk.injEq] using And.intro ha hb
  unfold run
  rw [hnorm]

theorem run_append (s : Nat × Nat) (xs ys : List U8) :
    run s (xs ++ ys) = run (run s xs) ys := by
  unfold run
  rw [List.foldl_append]
  exact congrArg (ys.foldl step) (normalize_run s xs).symm

end adler2
