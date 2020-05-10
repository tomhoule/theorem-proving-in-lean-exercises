
-- Working through section 7.1

namespace hidden

    inductive bool : Type
    | ff : bool
    | tt : bool

    def band (b1 b2 : bool) : bool :=
    bool.rec_on b1 bool.ff b2

    theorem t_and_f_is_f : band bool.tt bool.ff = bool.ff := rfl
    theorem f_and_t_is_f : band bool.ff bool.tt = bool.ff := rfl
    theorem f_and_f_is_f : band bool.ff bool.ff = bool.ff := rfl
    theorem t_and_t_is_t : band bool.tt bool.tt = bool.tt := rfl

    def bor (b1 b2 : bool) : bool :=
    bool.rec_on b1 b2 bool.tt

    theorem t_or_t_is_t : bor bool.tt bool.tt = bool.tt := rfl
    theorem t_or_f_is_t : bor bool.tt bool.ff = bool.tt := rfl
    theorem f_or_t_is_t : bor bool.ff bool.tt = bool.tt := rfl
    theorem f_or_f_is_f : bor bool.ff bool.ff = bool.ff := rfl

    def bnot (b : bool) : bool :=
    bool.rec_on b bool.tt bool.ff

    theorem not_t_is_f : bnot bool.tt = bool.ff := rfl
    theorem not_f_is_t : bnot bool.ff = bool.tt := rfl

end hidden

-- Going through section 7.2
--
-- > As exercises, we encourage you to develop a notion of composition for partial functions from α
-- > to β and β to γ, and show that it behaves as expected. We also encourage you to show that bool
-- > and nat are inhabited, that the product of two inhabited types is inhabited, and that the type
-- > of functions to an inhabited type is inhabited.

namespace chap7_section2

    variables { α β γ : Type }
    variables (a : α) (b : β) (c : γ)

    def and_then (f1 : α → option β) (f2 : β → option γ ) (a : α): option γ :=
    have option β, from f1 a,
    show option γ, from option.rec_on this none (λ b, f2 b)

    def return_none (α β : Type) : α → option β := λ _, none
    def return_some (α β : Type) : β → α → option β := λ b a, some b

    theorem none_none_none : and_then (return_none α β) (return_none β γ) a = none := rfl
    theorem none_some_none : and_then (return_none α β) (return_some β γ c) a = none := rfl
    theorem some_none_none : and_then (return_some α β b) (return_none β γ) a = none := rfl
    theorem some_some_some : and_then (return_some α β b) (return_some β γ c) a = some c := rfl

    theorem bool_inhabited : inhabited bool := inhabited.mk tt
    theorem nat_inhabited : inhabited ℕ := inhabited.mk 0
    theorem product_of_inhabited_is_inhabited : inhabited α → inhabited β → inhabited (α × β) :=
        λ alpha beta, inhabited.mk $ prod.mk alpha.default beta.default

    theorem type_of_functions_to_inhabited_type_is_inhabited : inhabited β → inhabited (α → β) :=
        λ hib, inhabited.mk $ λ a, hib.default

end chap7_section2

namespace ch7_section5
    universe u
    variables { α : Type }

    open list

    theorem append_nil (t : list α) : t ++ nil = t :=
    list.rec_on
        t
        (show nil ++ nil = nil, from nil_append (@nil α))
        (λ (hd: α) (tl: list α) (acc : tl ++ nil = tl),
            have e1 : hd::tl ++ nil = hd::(tl ++ nil), from cons_append hd tl nil,
            have e2 : hd::(tl ++ nil) = hd::tl, by rw [acc],
            show hd::tl ++ nil = hd::tl, by rw [e1, e2])

    theorem append_assoc (r s t : list α) :
    r ++ s ++ t = r ++ (s ++ t) :=
    list.rec_on
        r
        (show nil ++ s ++ t = nil ++ (s ++ t), by rw [nil_append, nil_append])
        (λ (hd : α) (tl : list α) (acc : tl ++ s ++ t = tl ++ (s ++ t)),
            calc
                ((hd::tl) ++ s) ++ t = hd::((tl ++ s) ++ t) : cons_append hd (tl ++ s) t
                                 ... = hd::(tl ++ (s ++ t)) : by rw [acc]
                                 ... = (hd::tl) ++ (s ++ t) : by rw [cons_append hd (tl)] )

    -- > Try also defining the function length : Π {α : Type u}, list α → nat that returns the
    -- > length of a list, and prove that it behaves as expected (for example, length (s ++ t) =
    -- > length s + length t).

    def length : list α → ℕ := λ xs, list.rec 0 (λ item list acc, acc + 1) xs

    theorem length_of_nil_is_zero : length (@nil α) = 0 := by refl
    theorem append_length (l1 l2 : list α) : length (l1 ++ l2) = length l1 + length l2 :=
    list.rec_on
        l1
        (
            have f1 : length (nil ++ l2) = length l2, by rw [nil_append],
            have f2 : length (@nil α) + length l2 = length l2, by rw [length_of_nil_is_zero, zero_add],
            show length (nil ++ l2) = length nil + length l2, by rw [f1, f2]
        )
        (λ (hd : α) (tl : list α) (acc : length (tl ++ l2) = length tl + length l2),
            have length (hd::tl) = length tl + 1, by refl,
            eq.symm $
            calc
                length (hd::tl) + length l2 = length tl + length l2 + 1 : by rw [this, add_assoc, add_comm 1, add_assoc]
                                        ... = length (tl ++ l2) + 1 : by rw [acc]
                                        ... = length (hd::tl ++ l2) : by refl
        )


    theorem cons_increases_len_by_1 (a : α) (l : list α) : length (list.cons a l) = length l + 1 := by refl

end ch7_section5

section ch7_section7
    universe u


    theorem mysymm {α : Type u} {a b : α} (h : eq a b) : eq b a :=
    eq.subst h (eq.refl a)

    theorem mytrans {α : Type u} {a b c : α}
    (h₁ : eq a b) (h₂ : eq b c) : eq a c :=
    eq.rec_on h₂ h₁

    theorem mycongr {α β : Type u} {a b : α} (f : α → β)
    (h : eq a b) : eq (f a) (f b) :=
    eq.rec_on h rfl

end ch7_section7
