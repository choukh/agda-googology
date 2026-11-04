# mk_inf.py 的逐模块补丁
import re
def sub(pat,rep,flags=0):
    return (lambda t: re.sub(pat,rep,t,flags=flags), None)
NOQ=sub(r' \{q′ = [^}]*\}','')
PATCHES={}
PATCHES['Rel']=[
("""data SameQ {m n : ℕ} (q : n <ᴸ m) : ∀ {n′} → n′ <ᴸ m → Set where
  same : SameQ q q

Sim∼ : ℕ → Fv → Fv → Set""","""record SameQ : Set where
  constructor same

Sim∼ : Ht → Fv → Fv → Set"""),
("""module _ (m : ℕ) (a b : Ordᴵ) (LR""","""module _ (m : Ht) (a b : Ordᴵ) (LR"""),
("""(Lv : ∀ {n n′} → n <ᴸ m → n′ <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n′ k′ ξ′ ζ′ → Set) where""","""(Lv : ∀ {n} → n <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n k′ ξ′ ζ′ → Set) where"""),
("""rcl : ∀ {φ χ ψ ρ n n′ κ₁ κ₂} {q : n <ᴸ m} {q′ : n′ <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n′) → Ev ℓ (κ₂ ⊔ fk zero)}""","""rcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}"""),
("""{g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n′ (κ₂ ⊔ fk η))} →
         SameQ q q′ → κ₁ ∼ᶠ κ₂ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (qcl q κ₁ s t g) (qcl q′ κ₂ s′ t′ g′)""","""{g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n (κ₂ ⊔ fk η))} →
         SameQ → κ₁ ∼ᶠ κ₂ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (qcl q κ₁ s t g) (qcl q κ₂ s′ t′ g′)"""),
("""rΩ↓ : ∀ {φ χ ψ ρ n n′ k k′} {q : n <ᴸ m} {q′ : n′ <ᴸ m} {fe""","""rΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe"""),
("""{ac′ : ∀ {L} → Ev L (ρ n′) → k′ <ᴵ L}""","""{ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}"""),
("""{h′ : ∀ ξ ζ → Vs m q′ k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n′ ζ ∪ ρ)} → SameQ q q′ → k ≅ᴵ k′""","""{h′ : ∀ ξ ζ → Vs m q k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → SameQ → k ≅ᴵ k′"""),
("""(∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → Sim∼ n′ ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n′ k′ ξ′ ζ′) → Lv q q′ z z′ → R₊ (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q′ z′))) → R₊ (qΩ↓ q fe ac h) (qΩ↓ q′ fe′ ac′ h′)""","""(∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Lv q z z′ → R₊ (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q z′))) → R₊ (qΩ↓ q fe ac h) (qΩ↓ q fe′ ac′ h′)"""),
("""Rq : ∀ m a b {φ χ ψ ρ} → Q m a φ χ → Q m b ψ ρ → Set
LRq : ∀ m a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → Q m k ξ ζ → Q m k′ ξ′ ζ′ → Set
LVq : ∀ m {n n′} → n <ᴸ m → n′ <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n′ k′ ξ′ ζ′ → Set
Rq m a b x y = R₊ m a b (LRq m a) (LVq m) x y
LRq m (suc k)   zero      {k′} x y = Rq m k k′ x y
LRq m (suc c)   (suc r)   x y = LRq m c r x y
LRq m (lim f s) (self n)  {k′} x y = Rq m (f n) k′ x y
LRq m (lim f s) (lim n r) x y = LRq m (f n) r x y
LVq (suc m) zero    zero     {k} {k′} x y = Rq m k k′ x y
LVq (suc m) zero    (suc q′) x y = ⊥
LVq (suc m) (suc q) zero     x y = ⊥
LVq (suc m) (suc q) (suc q′) x y = LVq m q q′ x y
""","""XR : Ht → Set₁
XR n = ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n k′ ξ′ ζ′ → Set

RV : ∀ m (v : ∀ {n} → n <ᴸ m → XR n) a b {φ χ ψ ρ} → Q m a φ χ → Q m b ψ ρ → Set
LRV : ∀ m (v : ∀ {n} → n <ᴸ m → XR n) a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → Q m k ξ ζ → Q m k′ ξ′ ζ′ → Set
RV m v a b x y = R₊ m a b (LRV m v a) v x y
LRV m v (suc k)   zero      {k′} x y = RV m v k k′ x y
LRV m v (suc c)   (suc r)   x y = LRV m v c r x y
LRV m v (lim f s) (self n)  {k′} x y = RV m v (f n) k′ x y
LRV m v (lim f s) (lim n r) x y = LRV m v (f n) r x y

FR : ∀ m → (∀ {n} → n <ᴸ m → XR n) → XR m
FR m v {k} {k′} x y = RV m v k k′ x y

LVq : ∀ m {n} → n <ᴸ m → XR n
LVq = Rec XR FR

Rq : ∀ m a b {φ χ ψ ρ} → Q m a φ χ → Q m b ψ ρ → Set
Rq m = RV m (LVq m)

LRq : ∀ m a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → Q m k ξ ζ → Q m k′ ξ′ ζ′ → Set
LRq m = LRV m (LVq m)
"""),
("""outVq : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → LVq m q q z z′ → Rq n k k′ z z′
outVq zero l = l
outVq (suc q) l = outVq q l

intoVq : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → Rq n k k′ z z′ → LVq m q q z z′
intoVq zero l = l
intoVq (suc q) l = intoVq q l
""","""outVq : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → LVq m q z z′ → Rq n k k′ z z′
outVq {m} q {z = z} {z′ = z′} l = subst (λ X → X z z′) (Rec-β XR FR m q) l

intoVq : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → Rq n k k′ z z′ → LVq m q z z′
intoVq {m} q {z = z} {z′ = z′} l = subst (λ X → X z z′) (sym (Rec-β XR FR m q)) l
"""),
("""lo∼ zero s i q = fz∼
lo∼ (suc H) s zero q = s zero (z<s H)
lo∼ {suc m} (suc H) {ζ} {ζ′} s (suc i) q = lo∼ {m} H {λ k → ζ (suc k)} {λ k → ζ′ (suc k)} (λ j r → s (suc j) (s<s r)) i (dn q)
""","""lo∼ H s i q with tri i H
... | tlt r = s i r
... | teq _ = fz∼
... | tgt _ = fz∼
"""),
("""upd∼ : ∀ {χ ρ : Fv} {x y} n → Sim∼ n χ ρ → x ∼ᶠ y → Sim∼ (suc n) (upd χ n x) (upd ρ n y)
upd∼ zero s c zero q = c
upd∼ zero s c (suc i) (suc ())
upd∼ (suc n) s c zero q = s zero (z<s n)
upd∼ {χ} {ρ} (suc n) s c (suc i) q = upd∼ {λ m → χ (suc m)} {λ m → ρ (suc m)} n (λ j r → s (suc j) (s<s r)) c i (dn q)
""","""cap∼ : ∀ {m} {χ ρ : Fv} {x y} n → Sim∼ n χ ρ → x ∼ᶠ y → Sim∼ m (cap χ n x) (cap ρ n y)
cap∼ n s c i q with tri i n
... | tlt r = s i r
... | teq _ = c
... | tgt _ = fz∼
"""),
(lambda t: re.sub(r"R-ι↓ : ∀ \{n k k′ α α′ φ ψ χ ρ\}.*?(?=\nR-tl : )", """R-ι↓ : ∀ {n m k k′ α α′ φ ψ χ ρ} (dq : n <ᴸ m) → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Rq m α α′ (ι↓ dq x) (ι↓ dq x′)
R-ι↓ dq ek rz = rz
R-ι↓ {n = n} dq ek (rs sa sb r) = rs sa (cap∼ n sb (flo-∼ ek)) (R-ι↓ dq ek r)
R-ι↓ dq ek (rl h) = rl (λ n → R-ι↓ dq ek (h n))
R-ι↓ dq ek (ri e h) = ri e (λ x y d → R-ι↓ dq ek (h x y d))
R-ι↓ dq ek (rŝ e r h) = rŝ e (R-ι↓ dq ek r) (λ η ee η′ e′ d → R-ι↓ dq ek (h η ee η′ e′ d))
R-ι↓ dq ek (rĉ e dz dg r h) = rĉ e dz dg (R-ι↓ dq ek r) (λ η ee η′ e′ d → R-ι↓ dq ek (h η ee η′ e′ d))
R-ι↓ dq ek (rclo s r h) = rclo s (R-ι↓ dq ek r) (λ η η′ d → R-ι↓ dq ek (h η η′ d))
R-ι↓ dq ek (rcl {q = q} same s r h) = rcl {q = tr< q dq} same s (R-ι↓ dq ek r) (λ η η′ d → rwk (R-ι↓ dq ek (h η η′ d)))
R-ι↓ dq ek (rwkˡ r) = rwkˡ (R-ι↓ dq ek r)
R-ι↓ dq ek (rwkʳ r) = rwkʳ (R-ι↓ dq ek r)
R-ι↓ {n = n} {m = m} {α = α} {α′ = α′} dq ek (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c f) =
  rΩ↓ {q = tr< q dq} same ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk
    (subst₂ (λ u v → Rq m α α′ (ι↓ dq (h ξ ζ (intoV q u))) (ι↓ dq (h′ ξ′ ζ′ (intoV q v)))) (sym (out-intoV (tr< q dq) z)) (sym (out-intoV (tr< q dq) z′))
      (R-ι↓ dq ek (f ξ ξ′ ζ ζ′ d dc dc′ _ _ (intoVq q (outVq (tr< q dq) l))))))
R-ι↓ {n = n} {m = m} {α = α} {α′ = α′} dq ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c f) =
  rΩ↓ {q = dq} same ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk
    (subst₂ (λ u v → Rq m α α′ (ι↓ dq (h ξ ζ (intoU (<→◃ r) u))) (ι↓ dq (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))) (sym (out-intoV dq z)) (sym (out-intoV dq z′))
      (R-ι↓ dq ek (f ξ ξ′ ζ ζ′ d dc _ _ (intoRq (<→◃ r) (outVq dq l))))))
R-ι↓ dq (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ dq ea l)
R-ι↓ dq (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)
""", t, flags=re.S), None),
("Rq 0 c c′ (tl {χ = χ} (flo k₁) cv a) (tl {χ = ρ} (flo k₂) cv′ b)","Rq h₀ c c′ (tl {χ = χ} (flo k₁) cv a) (tl {χ = ρ} (flo k₂) cv′ b)"),
("R-tl (s≅ le e) = rs (flo-∼ le) (λ i ()) (R-tl e)","R-tl (s≅ le e) = rs (flo-∼ le) (λ i q → ⊥-elim (no< q)) (R-tl e)"),
("Rq 0 c c′ (tl {χ = χ} φ cv (Ωˢ η)) (tl {χ = ρ} φ′ cv′ (Ωˢ η′))","Rq h₀ c c′ (tl {χ = χ} φ cv (Ωˢ η)) (tl {χ = ρ} φ′ cv′ (Ωˢ η′))"),
("R-tlΩ z≅ s = rs s (λ i ()) rz","R-tlΩ z≅ s = rs s (λ i q → ⊥-elim (no< q)) rz"),
("""RΩ̇ : ∀ m {a b} → a ≅ᴵ b → Rq m a b (Ω̇ m a) (Ω̇ m b)
RΩ̇ m (s≅ e) = rΩ e (⊔∼ fz∼ (fk∼ z≅)) Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e l (R-ι zero zero l)))
RΩ̇ m (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (RΩ̇ m (h n)) (R-ι (self n) (self n) (RΩ̇ m (h n))))
RΩ̇ zero z≅ = rclo (∼ᶠ-refl fz)
  (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
RΩ̇ (suc m) z≅ = rcl {q = zero} {q′ = zero} same fz∼ (rwk (R-ι↓ (s≅ z≅) (RΩ̇ m (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓ eη (RΩ̇ m eη)))
""","""XRΩ : Ht → Set
XRΩ m = ∀ {a b} → a ≅ᴵ b → Rq m a b (Ω̇ m a) (Ω̇ m b)

R-rowC : ∀ {m n} (q : n <ᴸ m) → XRΩ n → Rq m zero zero (rowC q (Ω̇ n)) (rowC q (Ω̇ n))
R-rowC q I = rcl {q = q} same fz∼ (rwk (R-ι↓ q (s≅ z≅) (I (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓ q eη (I eη)))

R-𝟏L : ∀ {m} → Rq m zero zero (𝟏L {m}) (𝟏L {m})
R-𝟏L = rwk (rs fz∼ (λ i q → fz∼) rz)

R-stepL : ∀ {m n} (q : n <ᴸ m) → XRΩ n → Rq m zero zero (stepL q (Ω̇ n)) (stepL q (Ω̇ n))
R-stepL q I = rwk (R-ι↓ q z≅ (I z≅))

R-rowL : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → (∀ {n} → n <ᴸ m → XRΩ n) → ∀ i → Rq m zero zero (rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i) (rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i)
R-rowL F qs₁ I zero = R-𝟏L
R-rowL {m} F qs₁ I (suc i) = subst (λ X → Rq m zero zero (stepL (qs₁ i) X) (stepL (qs₁ i) X)) (sym (ΩI≡ (qs₁ i))) (R-stepL (qs₁ i) (I (qs₁ i)))

R-row : ∀ m → (∀ {n} → n <ᴸ m → XRΩ n) → (v : View _<ᴸ_ h₀ m) → Rq m zero zero (rowV m (ΩI m) v) (rowV m (ΩI m) v)
R-row _ I base = rclo (∼ᶠ-refl fz)
  (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
R-row m I (clos q) = subst (λ X → Rq m zero zero (rowC q X) (rowC q X)) (sym (ΩI≡ q)) (R-rowC q (I q))
R-row m I (chain F qs₁) = rl (R-rowL F qs₁ I)

FRΩ : ∀ m → (∀ {n} → n <ᴸ m → XRΩ n) → XRΩ m
FRΩ m I (s≅ e) = rΩ e (⊔∼ fz∼ (fk∼ z≅)) Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e l (R-ι zero zero l)))
FRΩ m I (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (FRΩ m I (h n)) (R-ι (self n) (self n) (FRΩ m I (h n))))
FRΩ m I z≅ = R-row m I (view m)

RΩ̇ : ∀ m {a b} → a ≅ᴵ b → Rq m a b (Ω̇ m a) (Ω̇ m b)
RΩ̇ m = FRΩ m (Rec XRΩ FRΩ m)
"""),
NOQ,
("LVq m q q z z′","LVq m q z z′"),
("""out-intoV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} (z : Q n k ξ ζ) → outV q (intoV q z) ≡ z
out-intoV zero    z = refl
out-intoV (suc q) z = out-intoV q z
""",""),
]
def h0(t):
    t=t.replace('Cx 0 zero','Cx h₀ zero').replace('ClT 0 zero','ClT h₀ zero').replace('Rq 0 zero','Rq h₀ zero').replace('Q 0 zero','Q h₀ zero').replace('Gq g 0 zero','Gq g h₀ zero')
    return t
H0=(h0,None)
def pdlines(t):
    parts=re.split(r'(^```agda[ \t]*\n.*?^```)',t,flags=re.S|re.M)
    for j in range(1,len(parts),2):
        ls=parts[j].split('\n')
        out=[]
        for i,l in enumerate(ls):
            if '(pD o)' in l and ('ι↓' in l or (i+1<len(ls) and 'ι↓' in ls[i+1])):
                l=l.replace('(pD o)','(pD {q = qd} o)')
            if not l.lstrip().startswith('--'):
                l=l.replace('ι↓ {n = n} {α = zero} ','ι↓ {n = n} {α = zero} qd ')
                l=l.replace('ι↓ {α = zero} ','ι↓ {α = zero} qd ')
                l=re.sub(r'R-ι↓ (?!qd)','R-ι↓ qd ',l)
                l=re.sub(r'(?<![\w-])ι↓ (?!qd|\{)','ι↓ qd ',l)
            out.append(l)
        parts[j]='\n'.join(out)
    return ''.join(parts)
PD=(pdlines,None)
PATCHES['Cx']=[
("data Cx : ℕ → Ordᴵ → Flr → Fv → Set","data Cx : Ht → Ordᴵ → Flr → Fv → Set"),
H0,
("  pD  : ∀ {n k φ χ} → Cx (suc n) zero φ (upd χ n (flo k)) → Cx n k φ χ","  pD  : ∀ {n m k φ χ} {q : n <ᴸ m} → Cx m zero φ (cap χ n (flo k)) → Cx n k φ χ"),
("runᶜ (pD C)       x = runᶜ C (ι↓ x)","runᶜ (pD {q = q} C) x = runᶜ C (ι↓ q x)"),
("wkC {m = n} le lc (pD C) = pD (wkC le (upd-sub n lc (λ e → e)) C)","wkC {m = n} le lc (pD {q = q} C) = pD {q = q} (wkC le (upd-sub n lc (λ e → e)) C)"),
("run-wkC {m = n} le lc (pD C) x = run-wkC le (upd-sub n lc (λ e → e)) C (ι↓ x)","run-wkC {m = n} le lc (pD {q = q} C) x = run-wkC le (upd-sub n lc (λ e → e)) C (ι↓ q x)"),
("  pD  : ∀ {n k φ χ ψ ρ} {C : Cx (suc n) zero φ (upd χ n (flo k))} {C′ : Cx (suc n) zero ψ (upd ρ n (flo k))} → C ≈ᶜ C′ → pD C ≈ᶜ pD C′","  pD  : ∀ {n m k φ χ ψ ρ} {q : n <ᴸ m} {C : Cx m zero φ (cap χ n (flo k))} {C′ : Cx m zero ψ (cap ρ n (flo k))} → C ≈ᶜ C′ → pD {q = q} C ≈ᶜ pD {q = q} C′"),
("runᶜ-≅ (pD {k = k} o) r = runᶜ-≅ o (R-ι↓ (≅ᴵ-refl k) r)","runᶜ-≅ (pD {k = k} {q = q} o) r = runᶜ-≅ o (R-ι↓ q (≅ᴵ-refl k) r)"),
]
PATCHES['Rules']=[
PD,
("""ιD-cong : ∀ {n k φ χ ψ ρ} {x : Q n k φ χ} {y : Q n k ψ ρ} → x ⊑ᵀ y → ι↓ {α = zero} qd x ⊑ᵀ ι↓ {α = zero} qd y
ιD-cong h o = h (pD o)
""","""ιD-cong : ∀ {n m k φ χ ψ ρ} {qd : n <ᴸ m} {x : Q n k φ χ} {y : Q n k ψ ρ} → x ⊑ᵀ y → ι↓ {α = zero} qd x ⊑ᵀ ι↓ {α = zero} qd y
ιD-cong {qd = qd} h o = h (pD {q = qd} o)
"""),
]
PATCHES['Rules2']=[
PD,
("""Ω-rᵀ {m} {c = c} {χ = χ} {k = k} {x = x} {fe = fe} {r = r} {h = h} H (pD {q = qd} o) =
  Ω↓-rᵀ {x = ι↓ {α = zero} qd x} {q = zero} {fe = fe} {ac = λ e → cvFlo c (subst (Ev _) (upd-self χ m _) e) r} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo m ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoU (<→◃ r) z)))}
    (λ ξ ζ z rz f → wk-rᵀ (ιD-cong (H ξ ζ z rz f))) o""","""Ω-rᵀ {m} {c = c} {χ = χ} {k = k} {x = x} {fe = fe} {r = r} {h = h} H (pD {q = qd} o) =
  Ω↓-rᵀ {x = ι↓ {α = zero} qd x} {q = qd} {fe = fe} {ac = λ e → cvFlo c (subst (Ev _) (cap-self χ m _) e) r} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo m ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoU (<→◃ r) (outV qd z))))}
    (λ ξ ζ z rz f → wk-rᵀ (ιD-cong (subst (λ w → x ⊑ᵀ h ξ ζ (intoU (<→◃ r) w)) (sym (out-intoV qd z)) (H ξ ζ z rz f)))) o"""),
("""Ω↓-rᵀ {x = ι↓ {α = zero} qd x} {q = suc q} {fe = fe} {ac = λ e → ac (subst (Ev _) (upd-lt χ _ q) e)} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ qd (h ξ ζ z))} (λ ξ ζ z rz f → wk-rᵀ (ιD-cong (H ξ ζ z rz f))) o""","""Ω↓-rᵀ {x = ι↓ {α = zero} qd x} {q = tr< q qd} {fe = fe} {ac = λ e → ac (subst (Ev _) (cap-lt χ _ q) e)} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoV q (outV (tr< q qd) z))))} (λ ξ ζ z rz f → wk-rᵀ (ιD-cong (subst (λ w → x ⊑ᵀ h ξ ζ (intoV q w)) (sym (out-intoV (tr< q qd) z)) (H ξ ζ z rz f)))) o"""),
]
PATCHES['Rules3']=[PD,H0]
UPM=(lambda t: re.sub(r'upd-map n \(λ (\w+) e → e\) ','cap-map n ',t),None)
SZ=(lambda t: t.replace('sz (pD o′)','sz (pD {q = qd} o′)').replace('h2 z ez sz (pD {q = qd} o′)','h2 z ez sz (pD {q = qd} o′)'),None)
PATCHES['Strict']=[PD,UPM,
("shD {m = n} r (pD C) d = pD (wkC","shD {m = n} r (pD {q = q} C) d = pD {q = q} (wkC"),
]
PATCHES['Strict2']=[PD,UPM,SZ,
("""fz-upd : ∀ m i → fz ∼ᶠ upd (κ fz) m fz i
fz-upd zero zero = fz∼
fz-upd zero (suc i) = fz∼
fz-upd (suc m) zero = fz∼
fz-upd (suc m) (suc i) = fz-upd m i
""","""fz-upd : ∀ m i → fz ∼ᶠ cap (κ fz) m fz i
fz-upd m i with tri i m
... | tlt _ = fz∼
... | teq _ = fz∼
... | tgt _ = fz∼
"""),
("""R𝟏D : ∀ {n} k → Rq (suc n) zero zero (qs {φ = fz} {χ = κ fz} q0) (ι↓ {n = n} {α = zero} qd (𝟏q k))
R𝟏D {n} zero = rs fz∼ (λ i q → fz-upd n i) rz
R𝟏D (suc k) = rwkʳ (R𝟏D k)
R𝟏D (lim f s) = rwkʳ (R𝟏D (f 0))
""","""R𝟏D : ∀ {n m} (qd : n <ᴸ m) k → Rq m zero zero (qs {φ = fz} {χ = κ fz} q0) (ι↓ {n = n} {α = zero} qd (𝟏q k))
R𝟏D {n} qd zero = rs fz∼ (λ i q → fz-upd n i) rz
R𝟏D qd (suc k) = rwkʳ (R𝟏D qd k)
R𝟏D qd (lim f s) = rwkʳ (R𝟏D qd (f 0))
"""),
("""𝟏-D : ∀ {n k φ χ} {t : Q n k φ χ} → 𝟏q k ⊑ᵀ t → 𝟏q {suc n} zero ⊑ᵀ ι↓ {α = zero} qd t
𝟏-D {n} {k} h = ⊑ᵀ-Rˡʷ (λ _ → tt) (upd-sub n (λ i q _ → tt) (λ e → e)) (R𝟏D k) (ιD-cong h)
""","""𝟏-D : ∀ {n m k φ χ} {qd : n <ᴸ m} {t : Q n k φ χ} → 𝟏q k ⊑ᵀ t → 𝟏q {m} zero ⊑ᵀ ι↓ {α = zero} qd t
𝟏-D {n} {m} {k} {qd = qd} h = ⊑ᵀ-Rˡʷ (λ _ → tt) (upd-sub n (λ i q _ → tt) (λ e → e)) (R𝟏D qd k) (ιD-cong h)
"""),
("""𝟏⊑Ω̇ : ∀ m k → 𝟏q {m} k ⊑ᵀ Ω̇ m k
𝟏⊑Ω̇ zero zero = clo-rᵀ (qi-rᵀ (λ z d → wk-rᵀ (tl-cong {x = 𝟏} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ zero) (≅ˢ-sym d)))))
𝟏⊑Ω̇ (suc m) zero = cl-rᵀ (wk-rᵀ (𝟏-D (𝟏⊑Ω̇ m (suc zero))))
𝟏⊑Ω̇ m (suc k) = Ω-rᵀ (λ ξ ζ z rr f → wk-rᵀ (omk-go zero zero (R𝟏 k) (𝟏-up k zero) rr (R-ι zero zero rr) (λ o G′ → f (R𝟏 k) (𝟏⊑Ω̇ m k) (sh-≈ zero o) G′)))
𝟏⊑Ω̇ m (lim f s) = lim-rᵀ 0 (omk-go (self 0) (self 0) (R𝟏 (f 0)) (𝟏-up (f 0) (self 0)) (RΩ̇ m (≅ᴵ-refl _)) (R-ι (self 0) (self 0) (RΩ̇ m (≅ᴵ-refl _))) (λ o G′ → 𝟏⊑Ω̇ m (f 0) (sh-≈ (self 0) o) G′))
""","""-- ι↓ qd (Ω̇ n (suc a)) 的节点函数
Hι : ∀ {n m} (qd : n <ᴸ m) a ξ ζ → Q n a ξ ζ → Q m zero (ξ ⊔ Fl) (lo n ζ ∪ cap (κ Fl) n (flo (suc a)))
Hι {n} qd a ξ ζ z = qwk (λ e → e) (⇑ (c-∪ {lo n ζ} {κ Fl} _)) (ι↓ qd (qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero z (ι zero z))))

X𝟏 : Ht → Set
X𝟏 m = ∀ k → 𝟏q {m} k ⊑ᵀ Ω̇ m k

𝟏-rowC : ∀ {m n} (q : n <ᴸ m) → X𝟏 n → 𝟏q {m} zero ⊑ᵀ rowC q (Ω̇ n)
𝟏-rowC q I = cl-rᵀ (wk-rᵀ (𝟏-D (I (suc zero))))

𝟏-row : ∀ m → (∀ {n} → n <ᴸ m → X𝟏 n) → (v : View _<ᴸ_ h₀ m) → 𝟏q {m} zero ⊑ᵀ rowV m (ΩI m) v
𝟏-row _ I base = clo-rᵀ (qi-rᵀ (λ z d → wk-rᵀ (tl-cong {x = 𝟏} {y = z} (⊑ᴱ-≅ʳ (Ω1ᴱ zero) (≅ˢ-sym d)))))
𝟏-row m I (clos q) = subst (λ X → 𝟏q {m} zero ⊑ᵀ rowC q X) (sym (ΩI≡ q)) (𝟏-rowC q (I q))
𝟏-row m I (chain F qs₁) = lim-rᵀ 0 (wk-rᵀ (R→⊑ᵀ (R𝟏 zero)))

F𝟏 : ∀ m → (∀ {n} → n <ᴸ m → X𝟏 n) → X𝟏 m
F𝟏 m I zero = 𝟏-row m I (view m)
F𝟏 m I (suc k) = Ω-rᵀ (λ ξ ζ z rr f → wk-rᵀ (omk-go zero zero (R𝟏 k) (𝟏-up k zero) rr (R-ι zero zero rr) (λ o G′ → f (R𝟏 k) (F𝟏 m I k) (sh-≈ zero o) G′)))
F𝟏 m I (lim f s) = lim-rᵀ 0 (omk-go (self 0) (self 0) (R𝟏 (f 0)) (𝟏-up (f 0) (self 0)) (RΩ̇ m (≅ᴵ-refl _)) (R-ι (self 0) (self 0) (RΩ̇ m (≅ᴵ-refl _))) (λ o G′ → F𝟏 m I (f 0) (sh-≈ (self 0) o) G′))

𝟏⊑Ω̇ : ∀ m k → 𝟏q {m} k ⊑ᵀ Ω̇ m k
𝟏⊑Ω̇ m = F𝟏 m (Rec X𝟏 F𝟏 m)
"""),
("(λ d → R-ι↓ qd (≅ᴵ-refl _) (rf d))\n    (λ z d → 𝟏-D (h1 z d))","(λ d → R-ι↓ qd (≅ᴵ-refl _) (rf d))\n    (λ z d → 𝟏-D {qd = qd} (h1 z d))"),
]
PATCHES['Strict3']=[PD,UPM,SZ,
("""ClimbΩ {m} {c = c₀} {χ = χ} true {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pD {q = qd} o) c nd G′ =
  Climb↓ true {x = ι↓ {α = zero} qd x} {q = zero} {fe = fe} {ac = λ e → cvFlo c₀ (subst (Ev _) (upd-self χ m _) e) r} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo m ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoU (<→◃ r) z)))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ι↓ qd (≅ᴵ-refl c₀) (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    (λ ξ ζ z rz₁ f → wk-rᵀ (𝟏-D (h1 ξ ζ z rz₁ f)))
    (λ ξ ζ z rz₁ sz → Ls-wk true (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pD {q = qd} o′) c′ tt G))
    o c tt G′""","""ClimbΩ {m} {c = c₀} {χ = χ} true {x = x} {fe = fe} {r = r} {h = h} rf h1 h2 (pD {q = qd} o) c nd G′ =
  Climb↓ true {x = ι↓ {α = zero} qd x} {q = qd} {fe = fe} {ac = λ e → cvFlo c₀ (subst (Ev _) (cap-self χ m _) e) r} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo m ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoU (<→◃ r) (outV qd z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rq _ zero zero (ι↓ qd (h ξ ζ (intoU (<→◃ r) w))) (ι↓ qd (h ξ′ ζ′ (intoU (<→◃ r) w′)))) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (R-ι↓ qd (≅ᴵ-refl c₀) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))
    (λ ξ ζ z rz₁ f → wk-rᵀ (subst (λ w → Pos true (ι↓ {α = zero} qd (h ξ ζ (intoU (<→◃ r) w)))) (sym (out-intoV qd z)) (𝟏-D {qd = qd} (h1 ξ ζ z rz₁ f))))
    (λ ξ ζ z rz₁ sz → Ls-wk true (subst (λ w → Ls true (ι↓ {α = zero} qd x) (ι↓ {α = zero} qd (h ξ ζ (intoU (<→◃ r) w)))) (sym (out-intoV qd z)) (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pD {q = qd} o′) c′ tt G)))
    o c tt G′"""),
("""  Climb↓ true {x = ι↓ {α = zero} qd x} {q = suc q} {fe = fe} {ac = λ e → ac (subst (Ev _) (upd-lt χ _ q) e)} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ qd (h ξ ζ z))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ι↓ qd (≅ᴵ-refl c₀) (rf ξ ξ′ ζ ζ′ d dc z z′ l)))
    (λ ξ ζ z rz₁ f → wk-rᵀ (𝟏-D (h1 ξ ζ z rz₁ f)))
    (λ ξ ζ z rz₁ sz → Ls-wk true (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pD {q = qd} o′) c′ tt G))
    o c tt G′""","""  Climb↓ true {x = ι↓ {α = zero} qd x} {q = tr< q qd} {fe = fe} {ac = λ e → ac (subst (Ev _) (cap-lt χ _ q) e)} {h = λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ qd (h ξ ζ (intoV q (outV (tr< q qd) z))))}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rq _ zero zero (ι↓ qd (h ξ ζ (intoV q w))) (ι↓ qd (h ξ′ ζ′ (intoV q w′)))) (sym (out-intoV (tr< q qd) z)) (sym (out-intoV (tr< q qd) z′)) (R-ι↓ qd (≅ᴵ-refl c₀) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))
    (λ ξ ζ z rz₁ f → wk-rᵀ (subst (λ w → Pos true (ι↓ {α = zero} qd (h ξ ζ (intoV q w)))) (sym (out-intoV (tr< q qd) z)) (𝟏-D {qd = qd} (h1 ξ ζ z rz₁ f))))
    (λ ξ ζ z rz₁ sz → Ls-wk true (subst (λ w → Ls true (ι↓ {α = zero} qd x) (ι↓ {α = zero} qd (h ξ ζ (intoV q w)))) (sym (out-intoV (tr< q qd) z)) (λ o′ c′ _ G → h2 ξ ζ z rz₁ sz (pD {q = qd} o′) c′ tt G)))
    o c tt G′"""),
(lambda t: re.sub(r"Ω↓≺ : ∀ n a → Ls true.*?(?=\n```)", """Ω↓≺ : ∀ {n m} (qd : n <ᴸ m) a → Ls true (ι↓ {α = zero} qd (Ω̇ n a)) (ι↓ {α = zero} qd (Ω̇ n (suc a)))
Ω↓≺ {n} {m} qd a =
  Climb↓ true {x = ι↓ {α = zero} qd (Ω̇ n a)} {q = qd}
    {h = λ ξ ζ z → Hι qd a ξ ζ (outV qd z)}
    (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m zero zero (Hι qd a ξ ζ w) (Hι qd a ξ′ ζ′ w′)) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (rwk (rwk (rwk (R-ι↓ qd (≅ᴵ-refl a) l)))))
    (λ ξ ζ z rz₁ f → subst (λ w → Pos true (Hι qd a ξ ζ w)) (sym (out-intoV qd z)) (wk-rᵀ (wk-rᵀ (wk-rᵀ (𝟏-D {qd = qd} (f (R𝟏 a) (𝟏⊑Ω̇ n a)))))))
    (λ ξ ζ z rz₁ sz → subst (λ w → Ls true (ι↓ {α = zero} qd (Ω̇ n a)) (Hι qd a ξ ζ w)) (sym (out-intoV qd z)) (Ls-wk true (Ls-wk true (Ls-wk true (λ o c _ G → sz (pD {q = qd} o) c tt G)))))
""", t, flags=re.S),None),
]
PATCHES['Class']=[PD,UPM,H0,
("""ιD-congᵗ : ∀ {n k φ χ ψ ρ} {x : Q n k φ χ} {y : Q n k ψ ρ} → x ⊑ᵗ y → ι↓ {α = zero} qd x ⊑ᵗ ι↓ {α = zero} qd y
ιD-congᵗ h o = h (pD o)""","""ιD-congᵗ : ∀ {n m k φ χ ψ ρ} {qd : n <ᴸ m} {x : Q n k φ χ} {y : Q n k ψ ρ} → x ⊑ᵗ y → ι↓ {α = zero} qd x ⊑ᵗ ι↓ {α = zero} qd y
ιD-congᵗ {qd = qd} h o = h (pD {q = qd} o)"""),
("(λ n o₂ → K n (pD o₂))","(λ n o₂ → K n (pD {q = qd} o₂))"),
]
PATCHES['ClassF']=[]
PATCHES['Good']=[H0,NOQ,
("ClT : ℕ → Ordᴵ → Flr → Fv → Set₁","ClT : Ht → Ordᴵ → Flr → Fv → Set₁"),
("module _ (m : ℕ) (c : Ordᴵ) (L :","module _ (m : Ht) (c : Ordᴵ) (L :"),
("""Gq : Gr → ∀ m c {φ χ} → ClT m c φ χ → Q m c φ χ → Set₁
LG : ∀ m c → Gr → ∀ {k} → k ◃ c → ∀ {ξ ζ} → ClT m k ξ ζ → Q m k ξ ζ → Set₁
LV : ∀ m {n} → n <ᴸ m → ∀ {k ξ ζ} → ClT n k ξ ζ → Q n k ξ ζ → Set₁
Gq g m c 𝓖 x = G₊ m c (LG m c) (LV m) g 𝓖 x
LG m (suc c)   g zero      𝓖 x = Gq g m c 𝓖 x
LG m (suc c)   g (suc r)   𝓖 x = LG m c g r 𝓖 x
LG m (lim f s) g (self n)  𝓖 x = Gq g m (f n) 𝓖 x
LG m (lim f s) g (lim n r) 𝓖 x = LG m (f n) g r 𝓖 x
LV (suc m) zero    {k} 𝓖 x = Gq g₂ m k 𝓖 x
LV (suc m) (suc q) 𝓖 x = LV m q 𝓖 x
""","""XG : Ht → Set₂
XG n = ∀ {k ξ ζ} → ClT n k ξ ζ → Q n k ξ ζ → Set₁

GV : Gr → ∀ m (v : ∀ {n} → n <ᴸ m → XG n) c {φ χ} → ClT m c φ χ → Q m c φ χ → Set₁
LGV : ∀ m (v : ∀ {n} → n <ᴸ m → XG n) c → Gr → ∀ {k} → k ◃ c → ∀ {ξ ζ} → ClT m k ξ ζ → Q m k ξ ζ → Set₁
GV g m v c 𝓖 x = G₊ m c (LGV m v c) v g 𝓖 x
LGV m v (suc c)   g zero      𝓖 x = GV g m v c 𝓖 x
LGV m v (suc c)   g (suc r)   𝓖 x = LGV m v c g r 𝓖 x
LGV m v (lim f s) g (self n)  𝓖 x = GV g m v (f n) 𝓖 x
LGV m v (lim f s) g (lim n r) 𝓖 x = LGV m v (f n) g r 𝓖 x

FG : ∀ m → (∀ {n} → n <ᴸ m → XG n) → XG m
FG m v {k} 𝓖 x = GV g₂ m v k 𝓖 x

LV : ∀ m {n} → n <ᴸ m → XG n
LV = Rec XG FG

Gq : Gr → ∀ m c {φ χ} → ClT m c φ χ → Q m c φ χ → Set₁
Gq g m = GV g m (LV m)

LG : ∀ m c → Gr → ∀ {k} → k ◃ c → ∀ {ξ ζ} → ClT m k ξ ζ → Q m k ξ ζ → Set₁
LG m = LGV m (LV m)
"""),
("""outGV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} {𝓖 : ClT n k ξ ζ} {z : Q n k ξ ζ} → LV m q 𝓖 z → Gq g₂ n k 𝓖 z
outGV zero    x = x
outGV (suc q) x = outGV q x

intoGV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} {𝓖 : ClT n k ξ ζ} {z : Q n k ξ ζ} → Gq g₂ n k 𝓖 z → LV m q 𝓖 z
intoGV zero    x = x
intoGV (suc q) x = intoGV q x
""","""outGV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} {𝓖 : ClT n k ξ ζ} {z : Q n k ξ ζ} → LV m q 𝓖 z → Gq g₂ n k 𝓖 z
outGV {m} q {𝓖 = 𝓖} {z = z} x = subst (λ X → X 𝓖 z) (Rec-β XG FG m q) x

intoGV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} {𝓖 : ClT n k ξ ζ} {z : Q n k ξ ζ} → Gq g₂ n k 𝓖 z → LV m q 𝓖 z
intoGV {m} q {𝓖 = 𝓖} {z = z} x = subst (λ X → X 𝓖 z) (sym (Rec-β XG FG m q)) x
"""),
]
PATCHES['Vis']=[PD,UPM]
PATCHES['Read']=[PD,UPM,
("read1ᵀ (pD C) c t rt one G = read1ᵀ C c (ι↓ qd t) (R-ι↓ qd (≅ᴵ-refl _) rt) (𝟏-D one) G","read1ᵀ (pD {q = qd} C) c t rt one G = read1ᵀ C c (ι↓ qd t) (R-ι↓ qd (≅ᴵ-refl _) rt) (𝟏-D {qd = qd} one) G"),
("Twᵀ (pD C) c {y = y} ry one G = Twᵀ C c {y = ι↓ qd y} (R-ι↓ qd (≅ᴵ-refl _) ry) (𝟏-D one) G","Twᵀ (pD {q = qd} C) c {y = y} ry one G = Twᵀ C c {y = ι↓ qd y} (R-ι↓ qd (≅ᴵ-refl _) ry) (𝟏-D {qd = qd} one) G"),
]
for M in ['Iota','Tr','Add','Psi','PsiH','Eval']:
    PATCHES[M]=[NOQ,(lambda t: t.replace('Bd B ⊑ᴵ η → ℕ → Ordᴵ','Bd B ⊑ᴵ η → Ht → Ordᴵ'),None)]

NOLT=(lambda t: t.replace('(λ i ())','(λ i q₀ → ⊥-elim (no< q₀))'),None)

def tail_id(t):
    a=t.index('pD-refl : ∀ {n k φ χ ψ ρ}')
    b=t.index('```',a)
    head,sec,rest=t[:a],t[a:b],t[b:]
    # 取出 pD-refl 两行
    pr,sec=sec.split('\n\n',1)
    sec=sec.replace('{g′ n k φ χ}','{g′ k φ χ}')
    sec=sec.replace('{n = n} ','').replace('ID {g′} {n} {𝓖 = 𝓖}','ID {g′} {𝓖 = 𝓖}')
    for w in ['Sub','ClT','Cx']:
        sec=sec.replace(w+' (suc n)',w+' m')
    sec=sec.replace("Gq g′ (suc n)","Gq g′ m")
    sec=sec.replace("upd (upd χ j (ψ ⊔ fk η)) n (flo kᵈ)","cap (upd χ j (ψ ⊔ fk η)) n (flo kᵈ)")
    sec=sec.replace("upd (lo j ζ ∪ χ) n (flo kᵈ)","cap (lo j ζ ∪ χ) n (flo kᵈ)")
    sec=sec.replace("upd (lo n ζ ∪ χ) n (flo kᵈ)","cap (lo n ζ ∪ χ) n (flo kᵈ)")
    sec=re.sub(r'upd χ n \(flo','cap χ n (flo',sec)
    sec=re.sub(r'upd-map n \(λ (\w+) e → e\) ','cap-map n ',sec)
    sec=re.sub(r'(?<![\w-])pD (?!\{)','pD {q = qd} ',sec)
    sec=sec.replace('(pD {q = qd} D)','(pD {q = qd} D)')
    sec=re.sub(r'R-ι↓ (?!qd)','R-ι↓ qd ',sec)
    sec=re.sub(r'(?<![\w-])ι↓ (?!qd|\{)','ι↓ qd ',sec)
    sec=sec.replace('gΩ↓ {q = zero}','gΩ↓ {q = qd}')
    # gΩ↓ 行
    i=sec.index('ID {k = kᵈ} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ↓')
    j=sec.index('ID {k = suc a} {φ = φ} {χ = χ} {𝓖 = 𝓖} {𝓧 = 𝓧} H H₂ (gΩ {k = k₁}')
    c=sec[i:j]
    c=c.replace("""(λ ξ ζ {D} (x , c₀) u ru → subst (λ v → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ v) (run-wkC (λ e → e) (LL ζ) D (ι↓ qd (h ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru))""",
    """(λ ξ ζ {D} (x , c₀) u ru → subst (λ w → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ runᶜ D (H̃ ξ ζ w)) (sym (out-intoV Q′ u)) (subst (λ v → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ v) (run-wkC (λ e → e) (LL ζ) D (ι↓ qd (h ξ ζ (intoV q₁ u)))) (Wf ξ ζ c₀ u ru)))""")
    c=c.replace("""(λ 𝓔′ inc″ ξ ζ z rz₁ gz →
        gw (λ E""","""(λ 𝓔′ inc″ ξ ζ z rz₁ gz → subst (λ w → Gq _ m zero (𝓔′ ξ ζ) (H̃ ξ ζ w)) (sym (out-intoV Q′ z)) (
        gw (λ E""")
    c=c.replace("""(intoGV q₁ (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV q₁ gz))))))""","""(intoGV q₁ (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV Q′ gz)))))))""")
    c=c.replace("""(λ u → wk-lᵗ (wk-rᵗ (ιD-congᵗ (hm u))))""","""(λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ w w′ → H̃ ξ ζ w ⊑ᵗ H̃ ξ′ ζ′ w′) (sym (out-intoV Q′ z)) (sym (out-intoV Q′ z′)) (wk-lᵗ (wk-rᵗ (ιD-congᵗ (hm u)))))""")
    c=c.replace("""(λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ι↓ qd (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l)))""","""(λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m zero zero (H̃ ξ ζ w) (H̃ ξ′ ζ′ w′)) (sym (out-intoV Q′ z)) (sym (out-intoV Q′ z′)) (rwk (R-ι↓ qd (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))""")
    c=c.replace("""  where
  LL : ∀ ζ""","""  where
  Q′ = tr< q₁ qd
  LL : ∀ ζ""",1)
    c=c.replace("""  LL ζ = ⇑ (c-∪ {lo j ζ} {χ} _)
""","""  LL ζ = ⇑ (c-∪ {lo j ζ} {χ} _)
  H̃ : ∀ ξ ζ → Q j k₁ ξ ζ → Q m zero (ξ ⊔ φ) (lo j ζ ∪ cap χ n (flo kᵈ))
  H̃ ξ ζ w = qwk (λ e → e) (LL ζ) (ι↓ qd (h ξ ζ (intoV q₁ w)))
""")
    sec=sec[:i]+c+sec[j:]
    # gΩD
    i=sec.index('gΩD {k = kᵈ} {φ = φ} {χ = χ} {𝓖 = 𝓖}')
    c=sec[i:]
    c=c.replace("""(λ ξ ζ {D} (x , c₀) u ru → subst (λ v → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ v) (run-wkC (λ e → e) (LL ζ) D (ι↓ qd (h ξ ζ (intoU (<→◃ r) u)))) (Wf ξ ζ c₀ u ru))""",
    """(λ ξ ζ {D} (x , c₀) u ru → subst (λ w → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ runᶜ D (H̃ ξ ζ w)) (sym (out-intoV qd u)) (subst (λ v → runᶜ (W ξ ζ (pD {q = qd} (wkC (λ e → e) (LL ζ) D))) u ≅ˢ v) (run-wkC (λ e → e) (LL ζ) D (ι↓ qd (h ξ ζ (intoU (<→◃ r) u)))) (Wf ξ ζ c₀ u ru)))""")
    c=c.replace("""(λ 𝓔′ inc″ ξ ζ z rz₁ gz →
        gw (λ E""","""(λ 𝓔′ inc″ ξ ζ z rz₁ gz → subst (λ w → Gq _ m zero (𝓔′ ξ ζ) (H̃ ξ ζ w)) (sym (out-intoV qd z)) (
        gw (λ E""")
    c=c.replace("""(intoG (<→◃ r) (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) gz)))))""","""(intoG (<→◃ r) (Gmono (λ { (x , E , (D , c₁ , refl) , o) → x , D , c₁ , o }) (outGV qd gz)))))))""")
    c=c.replace("""(λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → wk-lᵗ (wk-rᵗ (ιD-congᵗ (hm u))))""","""(λ {ξ} {ξ′} {ζ} {ζ′} {z} {z′} u → subst₂ (λ w w′ → H̃ ξ ζ w ⊑ᵗ H̃ ξ′ ζ′ w′) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (wk-lᵗ (wk-rᵗ (ιD-congᵗ (hm u)))))""")
    c=c.replace("""(λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ι↓ qd (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l)))""","""(λ ξ ξ′ ζ ζ′ d dc z z′ l → subst₂ (λ w w′ → Rq m zero zero (H̃ ξ ζ w) (H̃ ξ′ ζ′ w′)) (sym (out-intoV qd z)) (sym (out-intoV qd z′)) (rwk (R-ι↓ qd (≅ᴵ-refl _) (rf ξ ξ′ ζ ζ′ d dc z z′ l))))""")
    c=c.replace("""  LL ζ = ⇑ (c-∪ {lo n ζ} {χ} _)
""","""  LL ζ = ⇑ (c-∪ {lo n ζ} {χ} _)
  H̃ : ∀ ξ ζ → Q n k₁ ξ ζ → Q m zero (ξ ⊔ φ) (lo n ζ ∪ cap χ n (flo kᵈ))
  H̃ ξ ζ w = qwk (λ e → e) (LL ζ) (ι↓ qd (h ξ ζ (intoU (<→◃ r) w)))
""")
    sec=sec[:i]+c
    sec='\n'.join(('  '+l if l.strip() else l) for l in sec.split('\n'))
    return head+pr+'\n\nmodule IDM {n m : Ht} (qd : n <ᴸ m) where\n'+sec+rest
PATCHES['Tail']=[H0,NOLT,
("""dmD : ∀ {n k X φ} {χ : Fv} → Dm n X φ χ → k ⊑ᴵ X → Dm (suc n) X φ (upd χ n (flo k))
dmD {n} {k} {X} {φ} {χ} (d₁ , d₂) u = d₁ , go
  where
  cst : ∀ {f f′ : Flr} → f′ ≡ f → (∀ {K} (r : InF K f) → Dem X r) → ∀ {K} (r : InF K f′) → Dem X r
  cst refl h r = h r
  go : ∀ i → i <ᴸ suc n → ∀ {K} (r : InF K (upd χ n (flo k) i)) → Dem X r
  go i zero = cst (upd-self χ n (flo k)) (λ r → demFlo r u)
  go i (suc l) = cst (upd-lt χ (flo k) l) (d₂ i l)
""","""dmD : ∀ {n m k X φ} {χ : Fv} → Dm n X φ χ → k ⊑ᴵ X → Dm m X φ (cap χ n (flo k))
dmD {n} {m} {k} {X} {φ} {χ} (d₁ , d₂) u = d₁ , go
  where
  cst : ∀ {f f′ : Flr} → f′ ≡ f → (∀ {K} (r : InF K f) → Dem X r) → ∀ {K} (r : InF K f′) → Dem X r
  cst refl h r = h r
  go : ∀ i → i <ᴸ m → ∀ {K} (r : InF K (cap χ n (flo k) i)) → Dem X r
  go i _ = case-tri i n
    (λ l → cst (cap-lt χ (flo k) l) (d₂ i l))
    (λ { refl → cst (cap-self χ n (flo k)) (λ r → demFlo r u) })
    (λ l → cst (cap-gt χ (flo k) l) (λ ()))
"""),
(tail_id,None),
]
PATCHES['Root']=[H0,NOLT,
("Ω̇G₀ : ∀ {g} → Gq g h₀ zero {Fl} 𝓥 (Ω̇ zero zero)","Ω̇G₀ : ∀ {g} → Gq g h₀ zero {Fl} 𝓥 (rowB {h₀})"),
("(read1 _ (Ctx-wkC C x) t et (fl (s≅ z≅ z≅) (Ω1ᴱ b)) G)","(read1 (tlo (wkC (λ v → toFlo zero (λ q → proj₂ v (suc q))) sub-id C)) (Ctx-wkC C x) t et (fl (s≅ z≅ z≅) (Ω1ᴱ b)) G)"),
]
def mono_down(t):
    a=t.index('D↑s : ∀ {n b}')
    b=t.index('## §4 `Up` 的单调')
    new='''D↑s : ∀ {m n b} → Sub m (cap (κ Fl) n (flo (suc b))) (cap (κ Fl) n (flo b))
D↑s {n = n} {b} = ⇑ (cap-map n (tighten zero))

D↑l : ∀ {m n f s} i → Sub m (cap (κ Fl) n (flo (lim f s))) (cap (κ Fl) n (flo (f i)))
D↑l {n = n} i = ⇑ (cap-map n (tighten (self i)))

Ωstep↓ : ∀ {n m b} {qd : n <ᴸ m} → ι↓ {α = zero} qd (Ω̇ n b) ⊑ᵀ ι↓ {α = zero} qd (Ω̇ n (suc b))
Ωstep↓ {n} {m} {b} {qd} = Ω↓-rᵀ {q = qd} (λ ξ ζ z rz₁ f → subst (λ w → ι↓ {α = zero} qd (Ω̇ n b) ⊑ᵀ Hι qd b ξ ζ w) (sym (out-intoV qd z)) (wk-rᵀ (wk-rᵀ (wk-rᵀ (ιD-cong (f (RΩ̇ n (≅ᴵ-refl b)) (R→⊑ᵀ (RΩ̇ n (≅ᴵ-refl b)))))))))

Ωlim↓ : ∀ {n m f s} {qd : n <ᴸ m} i → ι↓ {α = zero} qd (Ω̇ n (f i)) ⊑ᵀ ι↓ {α = zero} qd (Ω̇ n (lim f s))
Ωlim↓ {n} {m} {f} {qd = qd} i = lim-rᵀ i (wk-rᵀ (R→⊑ᵀ (R-ι↓ qd (≅ᴵ-refl (f i)) (RΩ̇ n (≅ᴵ-refl (f i))))))

Ωz↓ : ∀ {n m} {qd : n <ᴸ m} b → ι↓ {α = zero} qd (Ω̇ n zero) ⊑ᵀ ι↓ {α = zero} qd (Ω̇ n b)
Ωz↓ {n} {qd = qd} zero = R→⊑ᵀ (R-ι↓ qd z≅ (RΩ̇ n z≅))
Ωz↓ {qd = qd} (suc b) = ⊑ᵀ-transʷ (λ e → e) D↑s (Ωz↓ {qd = qd} b) (Ωstep↓ {qd = qd})
Ωz↓ {qd = qd} (lim g s) = ⊑ᵀ-transʷ (λ e → e) (D↑l 0) (Ωz↓ {qd = qd} (g 0)) (Ωlim↓ {qd = qd} 0)

Ωs↓ : ∀ {n m a₀ a″ b} {qd : n <ᴸ m} → a₀ ≅ᴵ a″ → a″ <ᴵ b → ι↓ {α = zero} qd (Ω̇ n (suc a₀)) ⊑ᵀ ι↓ {α = zero} qd (Ω̇ n b)
Ωs↓ {n} {qd = qd} e zero = R→⊑ᵀ (R-ι↓ qd (s≅ e) (RΩ̇ n (s≅ e)))
Ωs↓ {qd = qd} e (suc q) = ⊑ᵀ-transʷ (λ e₁ → e₁) D↑s (Ωs↓ {qd = qd} e q) (Ωstep↓ {qd = qd})
Ωs↓ {qd = qd} e (lim i q) = ⊑ᵀ-transʷ (λ e₁ → e₁) (D↑l i) (Ωs↓ {qd = qd} e q) (Ωlim↓ {qd = qd} i)

Ωm↓ : ∀ {n m a b} {qd : n <ᴸ m} → a ⊑ᴵ b → ι↓ {α = zero} qd (Ω̇ n a) ⊑ᵗ ι↓ {α = zero} qd (Ω̇ n b)
Ωm↓ {n} {b = b} {qd = qd} z⊑ = ⊑ᵀ→ᵗ (R-ι↓ qd z≅ (RΩ̇ n z≅)) (Ωz↓ {qd = qd} b)
Ωm↓ {n} {qd = qd} (s⊑ e q) = ⊑ᵀ→ᵗ (R-ι↓ qd (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _))) (Ωs↓ {qd = qd} e q)
Ωm↓ {qd = qd} (l⊑ k) = lim-lᵗ (λ i → wk-lᵗ (Ωm↓ {qd = qd} (k i)))
```

'''
    return t[:a]+new+t[b:]
PATCHES['Mono']=[(mono_down,None),UPM,
("shD≤ {n} {k} {k′} r r′ (pD {C = C₁} {C′ = C₁′} o) d d′ u {y} {y′} hy hy′ G G′ =","shD≤ {n} {k} {k′} r r′ (pD {q = qd} {C = C₁} {C′ = C₁′} o) d d′ u {y} {y′} hy hy′ G G′ ="),
("(Ωm↓ u (wk≈","(Ωm↓ {qd = qd} u (wk≈"),
("(hy {E₂ = pD (wkC","(hy {E₂ = pD {q = qd} (wkC"),
("(hy′ {E₂ = pD (wkC","(hy′ {E₂ = pD {q = qd} (wkC"),
]

OM_SEC12 = r'''## §1 高度 $n$ 的闭包守卫

对一个固定的 `qd : n <ᴸ m`. 原文件是 $m=n+1$.

```agda
lvG≡ : ∀ {u v : Ordˢ zero} → u ≡ v → (G : Goodᴺ (toZ v)) → Σ (Goodᴺ (toZ u)) λ G₁ → lvG G ≅ᴵ lvG G₁
lvG≡ refl G = G , ≅ᴵ-refl _

module BrM {n m : Ht} (qd : n <ᴸ m) where
  CD : Ordᴵ → Set
  CD k = Cx m zero Fl (cap (κ Fl) n (flo k))

  ι↓₀ : ∀ {k φ χ} → Q n k φ χ → Q m zero φ (cap χ n (flo k))
  ι↓₀ = ι↓ {α = zero} qd

  CQq : ∀ {ψ ρ} → Cx m zero ψ ρ → Ordᴵ → Set
  CQq C b = ∀ {k′} → k′ ≅ᴵ b → {D : CD k′} → D ≈ᶜ C → (G : Goodᴺ (toZ (runᶜ D (ι↓₀ (Ω̇ n k′))))) → suc b ⊑ᴵ lvG G

  record Brq {ψ ρ} (η : Ordᴵ) (C : Cx m zero ψ ρ) : Set where
    constructor br-mk
    field
      cxB : Ctxᶜ C
      br  : ∀ {b} → b ≺ᴵ η → CQq C b
      η₋  : Ordᴵ
      D₋  : CD η₋
      o₋  : D₋ ≈ᶜ C
      G₋  : Goodᴺ (toZ (runᶜ D₋ (ι↓₀ (Ω̇ n η₋))))
      eη  : η ≅ᴵ lvG G₋
      h₋  : η₋ ≺ᴵ η
  open Brq

  Ω↓lt : ∀ {a a′ b} → a ≅ᴵ a′ → (q : a′ <ᴵ b) → ι↓₀ (Ω̇ n a) ⊑ᵀ ι↓₀ (Ω̇ n b)
  Ω↓lt {a} {a′} {b} e q =
    ⊑ᵀ-transʷ (λ u → u) (⇑ (cap-map n (λ u {c} x → cvFlo b u (τ q x))))
      (⊑ᵀ-Rˡʷ (λ u → u) D↑s (R-ι↓ qd e (RΩ̇ n e)) (Ωstep↓ {qd = qd})) (Ωs↓ {qd = qd} (≅ᴵ-refl a′) q)

  Ω↓via : ∀ {a b} → a ≺ᴵ b → ι↓₀ (Ω̇ n a) ⊑ᵀ ι↓₀ (Ω̇ n b)
  Ω↓via (via e q) = Ω↓lt e q

  rdq : ∀ {η₀ k′ b} {D₀ : CD η₀} {D : CD k′} → D₀ ≈ᶜ D → (G₀ : Goodᴺ (toZ (runᶜ D₀ (ι↓₀ (Ω̇ n η₀))))) → b ≺ᴵ lvG G₀ →
        ι↓₀ (Ω̇ n η₀) ⊑ᵀ ι↓₀ (Ω̇ n k′) → (G : Goodᴺ (toZ (runᶜ D (ι↓₀ (Ω̇ n k′))))) → suc b ⊑ᴵ lvG G
  rdq {η₀} o G₀ h fl G =
    s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                           (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
    where
    L = fl o G
    d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) (R-ι↓ qd (≅ᴵ-refl η₀) (RΩ̇ n (≅ᴵ-refl η₀))))

  growT : ∀ {η₋ a η′} {D₋ : CD η₋} {D′ : CD η′} → Ctxᶜ D′ → D₋ ≈ᶜ D′ → η₋ ≅ᴵ a → (q : a <ᴵ η′) →
          (G₋ : Goodᴺ (toZ (runᶜ D₋ (ι↓₀ (Ω̇ n η₋))))) (G′ : Goodᴺ (toZ (runᶜ D′ (ι↓₀ (Ω̇ n η′))))) → lvG G₋ ≺ᴵ lvG G′
  growT {η₋} {a} {η′} {D₋} {D′} cD o e q G₋ G′ =
    ≺ᴵ-respˡ (toLevel-≅ (forceᴺ-HS _ G₋) (forceᴺ-HS _ (proj₁ S)) e₃)
             (toLevel-≺ (forceᴺ-HS _ (proj₁ S)) (forceᴺ-HS _ G′) (proj₂ L (proj₂ S)))
    where
    lS : Sub m (cap (κ Fl) n (flo η′)) (cap (κ Fl) n (flo (suc a)))
    lS = ⇑ (cap-map n (λ u {c} x → cvFlo η′ u (τ q x)))
    lA : Sub m (cap (κ Fl) n (flo η′)) (cap (κ Fl) n (flo a))
    lA = ⇑ (cap-map n (λ u → toFlo a (λ x → cvFlo η′ u (τ q (suc x)))))
    rD = ≈ᶜ-reflʳ o
    L = Ωs↓ {qd = qd} (≅ᴵ-refl a) q {C = wkC (λ u → u) lS D′} {C′ = D′} (≈ᶜ-wkˡ (λ u → u) lS rD) G′
    S = Ω↓≺ qd a {C = wkC (λ u → u) lA D′} {C′ = wkC (λ u → u) lS D′} (wk≈ (λ u → u) lA (λ u → u) lS rD) (Ctx-wkC D′ cD) tt (proj₁ L)
    e₃ = forceᴺ-≅ (toZ-≅ (runᶜ-≅ (≈ᶜ-wkʳ (λ u → u) lA o) (R-ι↓ qd e (RΩ̇ n e)))) G₋ (proj₁ S)

  brZ : ∀ {ψ ρ} {C : Cx m zero ψ ρ} → Ctxᶜ C → CQq C zero
  brZ x {k′} e {D} d G = read1ᵀ D (≈Ctxᶜ d x) (ι↓₀ (Ω̇ n k′)) (R-ι↓ qd (≅ᴵ-refl k′) (RΩ̇ n (≅ᴵ-refl k′))) (𝟏-D {qd = qd} (𝟏⊑Ω̇ n k′)) G

  ω1q : ∀ {k′ x L} → k′ ≅ᴵ x → x <ᴵ L → zero <ᴵ L → NZ x → ι↓₀ (Ω̇ n (suc zero)) ⊑ᵀ ι↓₀ (Ω̇ n k′)
  ω1q {k′} e q z nx = go (⊑ᴵ-≅ʳ (one⊑ z q nx) (≅ᴵ-sym e))
    where
    go : suc zero ⊑ᴵ k′ → ι↓₀ (Ω̇ n (suc zero)) ⊑ᵀ ι↓₀ (Ω̇ n k′)
    go (s⊑ z≅ r) = Ωs↓ {qd = qd} z≅ r

  ch₀q : ∀ (uₒ : Sub m (κ Fl) (cap (κ Fl) n (flo (suc zero)))) {C : Cx m zero Fl (κ Fl)} → 𝓥 C →
         (G : Goodᴺ (toZ (runᶜ C (qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero))))))) →
         ∀ {C′ : Cx m zero Fl (upd (κ Fl) n (fz ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brq (lvG G) C′
  ch₀q uₒ {C} x G {C′} x′ o = br-mk x′ brB (suc zero) D₁ (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym o)) G₁ e₁ two
    where
    J = lvG≡ (run-wkC (λ u → u) uₒ C (ι↓₀ (Ω̇ n (suc zero)))) G
    G₁ = proj₁ J
    e₁ = proj₂ J
    D₁ = wkC (λ u → u) uₒ C
    rt₁ : Rq m zero zero (qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero)))) (qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero))))
    rt₁ = rwk (R-ι↓ qd (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _)))
    one₁ : 𝟏q zero ⊑ᵀ qwk (λ u → u) uₒ (ι↓₀ (Ω̇ n (suc zero)))
    one₁ = wk-rᵀ (𝟏-D {qd = qd} (𝟏⊑Ω̇ n (suc zero)))
    two : suc zero ≺ᴵ lvG G
    two = toLevel-≺ (hs hz) (forceᴺ-HS _ G) (Twᵀ C x rt₁ one₁ G)
    z₁ : zero <ᴵ lvG G
    z₁ = zlt (read1ᵀ C x _ rt₁ one₁ G)
    brB : ∀ {b} → b ≺ᴵ lvG G → CQq C′ b
    brB {b = zero} h e d G′ = brZ x′ e d G′
    brB {b = suc b} h@(via eb qb) {k′} e {D} d G′ = rdq (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym (≈ᶜ-trans d o))) G₁ (≺ᴵ-respʳ h e₁) (ω1q (≅ᴵ-trans e eb) qb z₁ (NZ-≅₁ tt eb)) G′
    brB {b = lim f s} h@(via eb qb) {k′} e {D} d G′ = rdq (≈ᶜ-wkˡ (λ u → u) uₒ (≈ᶜ-sym (≈ᶜ-trans d o))) G₁ (≺ᴵ-respʳ h e₁) (ω1q (≅ᴵ-trans e eb) qb z₁ (NZ-≅₁ tt eb)) G′

  LLq : ∀ η → Sub m (upd (κ Fl) n (fz ⊔ fk η)) (cap (κ Fl) n (flo η))
  LLq η = ⇑ (upd-cap n (λ i e → e) (λ e → toFlo η (λ q → proj₂ e (suc q))))

  chSq : ∀ η {C : Cx m zero Fl (upd (κ Fl) n (fz ⊔ fk η))} → Brq η C →
         (G : Goodᴺ (toZ (runᶜ C (qwk (λ u → u) (LLq η) (ι↓₀ (Ω̇ n η)))))) →
         ∀ {C′ : Cx m zero Fl (upd (κ Fl) n (fz ⊔ fk (lvG G)))} → Ctxᶜ C′ → C′ ≈ᶜ C → Brq (lvG G) C′
  chSq η {C} B G {C′} x′ o = br-mk x′ brN η D₁ (≈ᶜ-wkˡ (λ u → u) (LLq η) (≈ᶜ-sym o)) G₁ e₁ (≺ᴵ-respʳ gr (≅ᴵ-sym e₁))
    where
    J = lvG≡ (run-wkC (λ u → u) (LLq η) C (ι↓₀ (Ω̇ n η))) G
    G₁ = proj₁ J
    e₁ = proj₂ J
    D₁ = wkC (λ u → u) (LLq η) C
    grr : η₋ B ≺ᴵ η → lvG (G₋ B) ≺ᴵ lvG G₁
    grr (via e′ q) = growT (Ctx-wkC C (cxB B)) (≈ᶜ-wkʳ (λ u → u) (LLq η) (o₋ B)) e′ q (G₋ B) G₁
    gr : η ≺ᴵ lvG G₁
    gr = ≺ᴵ-respˡ (eη B) (grr (h₋ B))
    brN : ∀ {b′} → b′ ≺ᴵ lvG G → CQq C′ b′
    brN {b′} h {k′} e {D} d G′ = go gr (≺ᴵ-respʳ h e₁)
      where
      dC : D ≈ᶜ C
      dC = ≈ᶜ-trans d o
      o₁ : D₁ ≈ᶜ D
      o₁ = ≈ᶜ-wkˡ (λ u → u) (LLq η) (≈ᶜ-sym dC)
      go : η ≺ᴵ lvG G₁ → b′ ≺ᴵ lvG G₁ → suc b′ ⊑ᴵ lvG G′
      go (via ex qx) h′@(via eb qb) with <ᴵ-dec qb qx
      ... | injᵃ s = br B (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ex))) e dC G′
      ... | injᵇ s = rdq o₁ G₁ h′ (Ω↓via (≺ᴵ-respˡ ex (≺ᴵ-respʳ s (≅ᴵ-sym (≅ᴵ-trans e eb))))) G′
      ... | injᶜ c = rdq o₁ G₁ h′ (R→⊑ᵀ (R-ι↓ qd (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym (≅ᴵ-trans e eb)))) (RΩ̇ n (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym (≅ᴵ-trans e eb))))))) G′

  BrCast : ∀ {η η′ ψ ρ ψ′ ρ′} {C : Cx m zero ψ ρ} {C′ : Cx m zero ψ′ ρ′} → η ≅ᴵ η′ → Ctxᶜ C′ → C′ ≈ᶜ C → Brq η C → Brq η′ C′
  BrCast eq x′ o B = br-mk x′ (λ h e d → br B (≺ᴵ-respʳ h (≅ᴵ-sym eq)) e (≈ᶜ-trans d o)) (η₋ B) (D₋ B) (≈ᶜ-trans (o₋ B) (≈ᶜ-sym o)) (G₋ B)
                           (≅ᴵ-trans (≅ᴵ-sym eq) (eη B)) (≺ᴵ-respʳ (h₋ B) eq)
```

## §2 下移读出闭包守卫

原文件的 `rt` 把上下文的头读出来再比较. 这里头的 `q` 要记住, 而 `≈ᶜ` 两边的 `q` 一样, 同时对两边模式匹配要用 K. 所以改成一个归纳的不变量 `Inv C₀ X`: $X$ 的头 (穿过搬运) 是 `pD {q = qd} C`, 且 $C\approx C_0$. 这与 `rt`, `rt-≈`, `rtD`, `rtE`, `InvD` 是同一个论证, 只是把它们合成了一个谓词.

```agda
  data Inv {ψ₀ ρ₀} (C₀ : Cx m zero ψ₀ ρ₀) : ∀ {k φ χ} → Cx n k φ χ → Set where
    iD  : ∀ {k φ χ} {C : Cx m zero φ (cap χ n (flo k))} → C ≈ᶜ C₀ → Inv C₀ (pD {q = qd} C)
    iT  : ∀ {a b φ χ} {e : a ≅ᴵ b} {C : Cx n b φ χ} → Inv C₀ C → Inv C₀ (ptr e C)
    iT⁻ : ∀ {a b φ χ} {e : a ≅ᴵ b} {C : Cx n a φ χ} → Inv C₀ C → Inv C₀ (ptr⁻ e C)

  Inv→Dd : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k φ χ} {X : Cx n k φ χ} → Inv C₀ X → Dd X
  Inv→Dd (iD c) = tt
  Inv→Dd (iT i) = Inv→Dd i
  Inv→Dd (iT⁻ i) = Inv→Dd i

  Inv-≈ : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k φ χ ψ ρ} {E : Cx n k φ χ} {X : Cx n k ψ ρ} → E ≈ᶜ X → Inv C₀ X → Inv C₀ E
  Inv-≈ (pD o) (iD c) = iD (≈ᶜ-trans o c)
  Inv-≈ (ptr o) (iT i) = iT (Inv-≈ o i)
  Inv-≈ (ptr⁻ o) (iT⁻ i) = iT⁻ (Inv-≈ o i)

  Inv-shD : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k ℓ φ χ} (r : k ◃₁ ℓ) {X : Cx n ℓ φ χ} (d : Dd X) → Inv C₀ X → Inv C₀ (shD r X d)
  Inv-shD r d (iD c) = iD (≈ᶜ-wkˡ (λ e → e) _ c)
  Inv-shD zero d (iT {e = s≅ e} i) = iT (Inv-shD zero d i)
  Inv-shD (self j) d (iT {e = l≅ h} i) = iT (Inv-shD (self j) d i)
  Inv-shD zero d (iT⁻ {e = s≅ e} i) = iT⁻ (Inv-shD zero d i)
  Inv-shD (self j) d (iT⁻ {e = l≅ h} i) = iT⁻ (Inv-shD (self j) d i)

  Inv-shE : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k ℓ φ χ} (r : k ◃₁ ℓ) (X : Cx n ℓ φ χ) (u : Nd X ⊎ Dd X) → Inv C₀ X → Inv C₀ (shE r X u)
  Inv-shE r X (inj₁ a) i = ⊥-elim (Nd∧Dd X a (Inv→Dd i))
  Inv-shE r X (inj₂ d) i = Inv-shD r d i

  InvD : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k b φ χ s} {X : Cx n k φ χ} {E : Cx n b Fl (κ Fl)} → Inv C₀ X → Sft X s E → Inv C₀ E
  InvD i (sB e) = Inv-≈ e i
  InvD {X = X} i (sS h) = InvD (Inv-shE zero X (dh X) i) h
  InvD {X = X} i (sL j h) = InvD (Inv-shE (self j) X (dh X) i) h
  InvD i (sT e h) = InvD (iT i) h
  InvD i (sT⁻ e h) = InvD (iT⁻ i) h

  inv-val : ∀ {ψ₀ ρ₀} {C₀ : Cx m zero ψ₀ ρ₀} {k} {E : Cx n k Fl (κ Fl)} → Inv C₀ E → {y : Q n k Fl (κ Fl)} → RΩv n k y →
            Σ Ordᴵ λ k₀ → Σ (CD k₀) λ D → (k₀ ≅ᴵ k) × (D ≈ᶜ C₀) × (runᶜ E y ≅ˢ runᶜ D (ι↓₀ (Ω̇ n k₀)))
  inv-val (iD {k = k} {C = C} c) hy = k , C , ≅ᴵ-refl k , c , hy (pD (≈ᶜ-reflˡ c))
  inv-val (iT {e = e} i) hy =
    let P = inv-val i (RΩv-tr e hy)
    in proj₁ P , proj₁ (proj₂ P) , ≅ᴵ-trans (proj₁ (proj₂ (proj₂ P))) (≅ᴵ-sym e) , proj₁ (proj₂ (proj₂ (proj₂ P))) , proj₂ (proj₂ (proj₂ (proj₂ P)))
  inv-val (iT⁻ {e = e} i) hy =
    let P = inv-val i (RΩv-tr⁻ e hy)
    in proj₁ P , proj₁ (proj₂ P) , ≅ᴵ-trans (proj₁ (proj₂ (proj₂ P))) e , proj₁ (proj₂ (proj₂ (proj₂ P))) , proj₂ (proj₂ (proj₂ (proj₂ P)))

  brVis : ∀ {η ψ ρ} {C₀ : Cx m zero ψ ρ} {Y : CD η} → Ctxᶜ Y → Y ≈ᶜ C₀ → (∀ {b} → b ≺ᴵ η → CQq C₀ b) → VisQ η (pD {q = qd} Y)
  brVis {η} x o br₁ = visQ x (λ {b} {E} h G →
    let P = inv-val (InvD (iD o) h) (RΩv-Ω {n} {b})
    in pull (proj₂ (proj₂ (proj₂ (proj₂ P)))) (λ H → br₁ (Sft-lvT h) (proj₁ (proj₂ (proj₂ P))) (proj₁ (proj₂ (proj₂ (proj₂ P)))) H) G)
  
  -- 闭包行的证书, 对低一层的 Ω̇G
  G-rowC : ∀ w → (∀ w′ → inp w′ ≡ w′ → ∀ k → Gq w′ n k (KQ w′ k) (Ω̇ n k)) → Gq w m zero 𝓥 (rowC qd (Ω̇ n))
  G-rowC w I =
    gcl 𝓥 (λ c → c) (λ η C → Brq η C) BrCast
       (gw (λ E → 𝓥 E × VisQ (suc zero) (pD {q = qd} E))
           (λ {C} c → Ctx-wkC C c , brVis (Ctx-wkC C c) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C c)) (λ { (via z≅ zero) → brZ c ; (via e (suc ())) }))
           (IDM.ID qd proj₂ proj₁ (I g₂ refl (suc zero))))
       (λ η → gw (λ E → 𝓥 E × VisQ η (pD {q = qd} E))
           (λ {C} B → Ctx-wkC C (cxB B) , brVis (Ctx-wkC C (cxB B)) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C (cxB B))) (br B))
           (IDM.ID qd proj₂ proj₁ (I g₂ refl η)))
       (rwk (R-ι↓ qd (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _))))
       (λ η η′ d → rwk (R-ι↓ qd d (RΩ̇ n d)))
       (λ η h → wk-lᵗ (wk-rᵗ (Ωm↓ {qd = qd} h)))
       (λ η η′ h u → wk-lᵗ (wk-rᵗ (Ωm↓ {qd = qd} u)))
       (λ c G ())
       (λ η c G ())
       (ch₀q _)
       chSq

  -- 链行的一项
  G-stepL : ∀ w → (∀ w′ → inp w′ ≡ w′ → ∀ k → Gq w′ n k (KQ w′ k) (Ω̇ n k)) → Gq w m zero 𝓥 (stepL qd (Ω̇ n))
  G-stepL w I =
    gw (λ E → 𝓥 E × VisQ zero (pD {q = qd} E))
       (λ {C} c → Ctx-wkC C c , brVis (Ctx-wkC C c) (≈ᶜ-wkˡ _ _ (ctxᶜ-refl C c)) (λ { (via e ()) }))
       (IDM.ID qd proj₂ proj₁ (I g₂ refl zero))
```

## §2′ 跨高度: 两次 `ι↓` 与一次

链行的单调. $\iota_{\downarrow q'}(\iota_{\downarrow r}x)$ 与 $\iota_{\downarrow (r;q')}x$ 互模拟. 中间一层的目标是 $0$, 地板 `flo zero` 是 `fz`, 所以地板一致. 嵌套节点的 $q$ 只差结合律 (`tr-assoc`).

```agda
cap²∼ : ∀ {a b c} {χ ρ : Fv} {x y} → a <ᴸ b → Sim∼ a χ ρ → x ∼ᶠ y → Sim∼ c (cap χ a x) (cap (cap ρ a y) b fz)
cap²∼ {a} {b} {c} {χ} {ρ} {x} {y} x₁ s e i q = case-tri i a
  (λ r → subst₂ _∼ᶠ_ (sym (cap-lt χ x r)) (sym (trans (cap-lt (cap ρ a y) fz (tr< r x₁)) (cap-lt ρ y r))) (s i r))
  (λ { refl → subst₂ _∼ᶠ_ (sym (cap-self χ i x)) (sym (trans (cap-lt (cap ρ i y) fz x₁) (cap-self ρ i y))) e })
  (λ r → case-tri i b
     (λ r′ → subst₂ _∼ᶠ_ (sym (cap-gt χ x r)) (sym (trans (cap-lt (cap ρ a y) fz r′) (cap-gt ρ y r))) fz∼)
     (λ { refl → subst₂ _∼ᶠ_ (sym (cap-gt χ x r)) (sym (cap-self (cap ρ a y) i fz)) fz∼ })
     (λ r′ → subst₂ _∼ᶠ_ (sym (cap-gt χ x r)) (sym (cap-gt (cap ρ a y) fz r′)) fz∼))

R-Ω↓-cast : ∀ {c α α′ j k k′ φ χ ψ ρ} {Q₁ Q₂ : j <ᴸ c} → Q₁ ≡ Q₂ → {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ j) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ j) → k′ <ᴵ L}
            {h₁ : ∀ ξ ζ → Vs c Q₁ k ξ ζ → Q c α (ξ ⊔ φ) (lo j ζ ∪ χ)} {h₂ : ∀ ξ ζ → Vs c Q₂ k′ ξ ζ → Q c α′ (ξ ⊔ ψ) (lo j ζ ∪ ρ)} →
            k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ c χ ρ →
            (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ j ζ ζ′ → (z : Q j k ξ ζ) (z′ : Q j k′ ξ′ ζ′) → Rq j k k′ z z′ → Rq c α α′ (h₁ ξ ζ (intoV Q₁ z)) (h₂ ξ′ ζ′ (intoV Q₂ z′))) →
            Rq c α α′ (qΩ↓ Q₁ fe ac h₁) (qΩ↓ Q₂ fe′ ac′ h₂)
R-Ω↓-cast {Q₁ = Q₁} refl ek s c f = rΩ↓ {q = Q₁} same ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → f ξ ξ′ ζ ζ′ d dc z z′ (outVq Q₁ l))

R-cl-cast : ∀ {c α α′ j φ χ ψ ρ κ₁ κ₂} {Q₁ Q₂ : j <ᴸ c} → Q₁ ≡ Q₂ → {s : ∀ {ℓ} → Ev ℓ (χ j) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ j) → Ev ℓ (κ₂ ⊔ fk zero)}
            {t : Q c α φ χ} {t′ : Q c α′ ψ ρ} {g : (η : Ordᴵ) → Q c α φ (upd χ j (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q c α′ ψ (upd ρ j (κ₂ ⊔ fk η))} →
            κ₁ ∼ᶠ κ₂ → Rq c α α′ t t′ → (∀ η η′ → η ≅ᴵ η′ → Rq c α α′ (g η) (g′ η′)) → Rq c α α′ (qcl Q₁ κ₁ s t g) (qcl Q₂ κ₂ s′ t′ g′)
R-cl-cast {Q₁ = Q₁} refl e r h = rcl {q = Q₁} same e r h

R-ιι↓ : ∀ {a b c k k′ α α′ φ ψ χ ρ} (x₁ : a <ᴸ b) (x₂ : b <ᴸ c) → k ≅ᴵ k′ → {x : Q a k φ χ} {x′ : Q a k′ ψ ρ} → Rq a k k′ x x′ →
        Rq c α α′ (ι↓ (tr< x₁ x₂) x) (ι↓ {k = zero} x₂ (ι↓ {α = zero} x₁ x′))
R-ιι↓ x₁ x₂ ek rz = rz
R-ιι↓ x₁ x₂ ek (rs sa sb r) = rs sa (cap²∼ x₁ sb (flo-∼ ek)) (R-ιι↓ x₁ x₂ ek r)
R-ιι↓ x₁ x₂ ek (rl h) = rl (λ n → R-ιι↓ x₁ x₂ ek (h n))
R-ιι↓ x₁ x₂ ek (ri e h) = ri e (λ x y d → R-ιι↓ x₁ x₂ ek (h x y d))
R-ιι↓ x₁ x₂ ek (rŝ e r h) = rŝ e (R-ιι↓ x₁ x₂ ek r) (λ η ee η′ e′ d → R-ιι↓ x₁ x₂ ek (h η ee η′ e′ d))
R-ιι↓ x₁ x₂ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ιι↓ x₁ x₂ ek r) (λ η ee η′ e′ d → R-ιι↓ x₁ x₂ ek (h η ee η′ e′ d))
R-ιι↓ x₁ x₂ ek (rclo s r h) = rclo s (R-ιι↓ x₁ x₂ ek r) (λ η η′ d → R-ιι↓ x₁ x₂ ek (h η η′ d))
R-ιι↓ x₁ x₂ ek (rcl {q = q} same s r h) =
  R-cl-cast (sym (tr-assoc q x₁ x₂)) s (R-ιι↓ x₁ x₂ ek r) (λ η η′ d → rwkˡ (rwkʳ (rwkʳ (R-ιι↓ x₁ x₂ ek (h η η′ d)))))
R-ιι↓ x₁ x₂ ek (rwkˡ r) = rwkˡ (R-ιι↓ x₁ x₂ ek r)
R-ιι↓ x₁ x₂ ek (rwkʳ r) = rwkʳ (R-ιι↓ x₁ x₂ ek r)
R-ιι↓ {a} {b} {c} {α = α} {α′ = α′} x₁ x₂ ek (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c′ f) =
  R-Ω↓-cast (sym (tr-assoc q x₁ x₂)) ei s (cap²∼ x₁ c′ (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwkˡ (rwkʳ (rwkʳ
    (subst₂ (λ u v → Rq c α α′ (ι↓ (tr< x₁ x₂) (h ξ ζ (intoV q u))) (ι↓ {k = zero} x₂ (ι↓ {α = zero} x₁ (h′ ξ′ ζ′ (intoV q v)))))
       (sym (out-intoV (tr< q (tr< x₁ x₂)) z))
       (sym (trans (cong (λ w → outV (tr< q x₁) (intoV (tr< q x₁) w)) (out-intoV (tr< (tr< q x₁) x₂) z′)) (out-intoV (tr< q x₁) z′)))
       (R-ιι↓ x₁ x₂ ek (f ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq q l)))))))
R-ιι↓ {a} {b} {c} {α = α} {α′ = α′} x₁ x₂ ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c′ f) =
  R-Ω↓-cast refl ei s (cap²∼ x₁ c′ (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwkˡ (rwkʳ (rwkʳ
    (subst₂ (λ u v → Rq c α α′ (ι↓ (tr< x₁ x₂) (h ξ ζ (intoU (<→◃ r) u))) (ι↓ {k = zero} x₂ (ι↓ {α = zero} x₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))))
       (sym (out-intoV (tr< x₁ x₂) z))
       (sym (trans (cong (λ w → outV x₁ (intoV x₁ w)) (out-intoV (tr< x₁ x₂) z′)) (out-intoV x₁ z′)))
       (R-ιι↓ x₁ x₂ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l)))))))
R-ιι↓ x₁ x₂ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwkˡ (rwkʳ (R-ιι↓ x₁ x₂ ea l))
R-ιι↓ x₁ x₂ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwkˡ (rwkʳ (R-ιι↓ x₁ x₂ ea l))

-- 第 0 行开出来是闭包时, ι↓ (Ω̇ n 0) 在它下面
Ω̇-clos : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → Ω̇ m zero ≡ rowC r (Ω̇ n)
Ω̇-clos {n} {m} r e = trans (cong (rowV m (ΩI m)) e) (cong (rowC r) (ΩI≡ r))

ι↓⊑row : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ Ω̇ m zero
ι↓⊑row {n} {m} r e = subst (λ X → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ X) (sym (Ω̇-clos r e)) (cl-rᵀ (wk-rᵀ (Ωz↓ {qd = r} (suc zero))))

step-mono : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → view n′ ≡ clos r → stepL (tr< r q′) (Ω̇ n) ⊑ᵗ stepL q′ (Ω̇ n′)
step-mono {n} {n′} {m} r q′ e =
  wk-lᵗ (wk-rᵗ (⊑ᵀ→ᵗ (R-ι↓ (tr< r q′) z≅ (RΩ̇ n z≅))
    (⊑ᵀ-Rˡʷ (λ u → u) (upd-sub n′ (λ i q u → κ-cap n (λ _ → tt) i u) (λ u → u)) (R-ιι↓ r q′ z≅ (RΩ̇ n z≅)) (ιD-cong {qd = q′} (ι↓⊑row r e)))))
```

'''
def om_row(t):
    a=t.index('## §1 高度 $n$ 的闭包守卫')
    b=t.index('## §3 $\\dot\\Omega$ 全体')
    t=t[:a]+OM_SEC12+t[b:]
    # 第 3 节
    a=t.index("Ω̇G′ : ∀ w → inp w ≡ w → ∀ m k → Gq w m k (KQ w k) (Ω̇ m k)")
    b=t.index("Ω̇G′ w iw m (suc k) =")
    t=t[:a]+'''XG′ : Ht → Set₁
XG′ m = ∀ w → inp w ≡ w → ∀ k → Gq w m k (KQ w k) (Ω̇ m k)

-- 链行第 0 项: 1
G-𝟏L : ∀ w {m} → Gq w m zero 𝓥 (𝟏L {m})
G-𝟏L w = gw 𝓥 (λ {C} c → Ctx-wkC C c)
  (gs 𝓥 (λ c → c) g0 (λ _ f _ → cxoᵀ f) (λ x o _ → x) (λ _ _ → (λ ()) , (λ i q ())) (λ c → Hq-zero _))

G-rowL : ∀ w {m} F (qs₁ : ∀ i → F i <ᴸ m) → (∀ {n} → n <ᴸ m → XG′ n) → ∀ i → Gq w m zero 𝓥 (rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i)
G-rowL w F qs₁ I zero = G-𝟏L w
G-rowL w {m} F qs₁ I (suc i) = subst (λ X → Gq w m zero 𝓥 (stepL (qs₁ i) X)) (sym (ΩI≡ (qs₁ i))) (BrM.G-stepL (qs₁ i) w (I (qs₁ i)))

mono-rowL : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → view m ≡ chain F qs₁ → ∀ i → rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i ⊑ᵗ rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) (suc i)
mono-rowL {m} F qs₁ ev zero = subst (λ X → 𝟏L {m} ⊑ᵗ stepL (qs₁ 0) X) (sym (ΩI≡ (qs₁ 0)))
  (⊑ᵀ→ᵗ R-𝟏L (wk-lᵀ (wk-rᵀ (𝟏-D {qd = qs₁ 0} (𝟏⊑Ω̇ (F 0) zero)))))
mono-rowL {m} F qs₁ ev (suc i) with view-step ev i
... | r , vw , qe = subst₂ (λ X Y → stepL (qs₁ i) X ⊑ᵗ stepL (qs₁ (suc i)) Y) (sym (ΩI≡ (qs₁ i))) (sym (ΩI≡ (qs₁ (suc i))))
  (subst (λ q₀ → stepL q₀ (Ω̇ (F i)) ⊑ᵗ stepL (qs₁ (suc i)) (Ω̇ (F (suc i)))) (sym qe) (step-mono r (qs₁ (suc i)) vw))

rowG : ∀ w m → (∀ {n} → n <ᴸ m → XG′ n) → (v : View _<ᴸ_ h₀ m) → view m ≡ v → Gq w m zero (KQ w zero) (rowV m (ΩI m) v)
rowG w _ I base _ = Gmono (KQ→Ctx w) Ω̇G₀
rowG w m I (clos q) _ = subst (λ X → Gq w m zero (KQ w zero) (rowC q X)) (sym (ΩI≡ q)) (Gmono (KQ→Ctx w) (BrM.G-rowC q w (I q)))
rowG w m I (chain F qs₁) ev = Gmono (KQ→Ctx w) (gl (G-rowL w F qs₁ I) (mono-rowL F qs₁ ev))

FG′ : ∀ m → (∀ {n} → n <ᴸ m → XG′ n) → XG′ m
FG′ m I w iw zero = rowG w m I (view m) refl
'''+t[b:]
    a=t.index("Ω̇G′ w iw m (suc k) =")
    t=t[:a]+t[a:].replace("Ω̇G′ w iw m (suc k) =","FG′ m I w iw (suc k) =",1)
    t=t.replace("Ω̇G′ w iw m (lim f s) =","FG′ m I w iw (lim f s) =")
    t=t.replace("(Ω̇G′ g₂ refl m (f i))","(FG′ m I g₂ refl (f i))")
    t=t.replace("(Ω̇G′ w iw m (f i))","(FG′ m I w iw (f i))")
    t=t.replace("""Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)
Ω̇G g m k = Ω̇G′ (inp g) (inp-idem g) m k""","""Ω̇G′ : ∀ m → XG′ m
Ω̇G′ m = FG′ m (Rec XG′ FG′ m)

Ω̇G : ∀ g m k → Gq (inp g) m k (KQ (inp g) k) (Ω̇ m k)
Ω̇G g m k = Ω̇G′ m (inp g) (inp-idem g) k""")
    t=t.replace("""sh≡D {m = n} zero (pD C) d z x = run-wkC (λ e → e) (⇑ (upd-map n (λ i e → e) (tighten zero))) C (ι↓ z)
sh≡D {m = n} (self i) (pD C) d z x = run-wkC (λ e → e) (⇑ (upd-map n (λ i₁ e → e) (tighten (self i)))) C (ι↓ z)""","""sh≡D {m = n} zero (pD {q = qd} C) d z x = run-wkC (λ e → e) (⇑ (cap-map n (tighten zero))) C (ι↓ qd z)
sh≡D {m = n} (self i) (pD {q = qd} C) d z x = run-wkC (λ e → e) (⇑ (cap-map n (tighten (self i)))) C (ι↓ qd z)""")
    return t
PATCHES['Omega']=[(om_row,None),("open import OCF.Free.Floor using (⊔∼; fk∼)","open import OCF.Free.Floor using (⊔∼; fk∼; fz∼)")]
