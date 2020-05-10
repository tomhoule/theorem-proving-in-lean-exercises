
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
