 def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ doubler, λ original, doubler $ doubler original


-- Exercise 1

def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
def double (n : ℕ) : ℕ := n * 2

-- test
def doubling_two_twice : ℕ := do_twice double 2

#reduce doubling_two_twice
#reduce Do_Twice do_twice double 2

-- Exercise 2

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ (a: α), λ (b: β), f (a, b)
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ (pair : (α × β)), f pair.1 pair.2

#check curry
#check uncurry

-- Exercise 3

namespace vecadd

    universe u

    constant vec : Type u -> ℕ -> Type u
    constant vec_add : Π { len : ℕ }, vec ℕ len -> vec ℕ len -> vec ℕ len

    #check vec_add

    constant vec_reverse : Π { α : Type } { len: ℕ }, vec α len -> vec α len

    #check vec_reverse

    #check let add_vecs_then_reverse := λ (len : nat) (v1 : vec _ len) v2, vec_reverse (vec_add v1 v2)
        in add_vecs_then_reverse
end vecadd

-- Exercise 4
