# 折叠是和的作用 (二): 和与树的对应

> 不含记号. 入口 [TLRule](TLRule.lagda.md). `Rel L b x y`: 第 $L$ 层, 旧树 (`CumReadCF` 的数据树) 从 $b$ 走新树 $x$ 到 $y$. 旧树只用来量值. 这一篇是对应的规则和它们的闭包性质, 不含折叠.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleRel where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import OCF.Align.CumReadCF
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (_⊴_; rf; s; l; nd; eR; eL; ψL; add-mono; add⊴; rep⊴; z⊴; Ω⊴)
import OCF.Align.TLRuleSum as N
open N using (D; n0; n1; _⨾_; nl; ni; Int; Ipt; AccL; acc; accL; ≪≪; Dif; Ωd)
```

## §1 分支的连续性

`ContF κ H`: 函数 $H$ 从 $k$ 层的旧树到 $M$ 层的旧树, 保 `≈`, 保第一位置, 过极限, 过更低的节点. $\kappa$ 是节点路径的搬运.

```agda
record ContF {k M : A} (κ : ∀ {j} → j ≪ k → j ≪ M) (H : O k → O M) : Set where
  field
    cq : ∀ {z z′} → z ≈ z′ → H z ≈ H z′
    cl : ∀ {z} (g : ℕ → O k) → z ≈ ol g → H z ≈ ol (λ n → H (g n))
    cn : ∀ {z j} (s₁ : j ≪ k) (g : O j → O k) → z ≈ oi s₁ (λ y → g (outS (≪S s₁) y)) → (∀ {a a′} → a ≈ a′ → g a ≈ g a′) →
         H z ≈ oi (κ s₁) (λ y → H (g (outS (≪S (κ s₁)) y)))
    cm : ∀ {z z′} → z ⊴ z′ → H z ⊴ H z′
open ContF public

comp : ∀ {k M N₁} {κ₁ : ∀ {j} → j ≪ k → j ≪ M} {κ₂ : ∀ {j} → j ≪ M → j ≪ N₁} {H₁ : O k → O M} {H₂ : O M → O N₁} →
       ContF κ₁ H₁ → ContF κ₂ H₂ → ContF (λ r → κ₂ (κ₁ r)) (λ z → H₂ (H₁ z))
comp C₁ C₂ = record
  { cq = λ e → cq C₂ (cq C₁ e)
  ; cl = λ g e → cl C₂ (λ n → _) (cl C₁ g e)
  ; cn = λ s₁ g e q → cn C₂ _ _ (cn C₁ s₁ g e q) (λ d → cq C₁ (q d))
  ; cm = λ d → cm C₂ (cm C₁ d)
  }
```

## §2 关系

`rl`: $\sum_n d_n$ 对上 $\lim g$, $g$ 的相邻项由 $d_n$ 走到. `rd`: 上确界多一个头 $g_0\trianglelefteq g_1$. `ri`: $\sum_w u(w)$ 对上节点, $H$ 是节点的分支; 第一支是 $b$, 每走一格, 分支走 $u(w)$.

```agda
module _ (L : A) (Lw : ∀ {a} → Strict a L → O a → D a → O a → Set) where
  data Rel₊ : O L → D L → O L → Set where
    rz : ∀ {b y} → b ≈ y → y ≈ y → Rel₊ b n0 y
    rs : ∀ {b y} → y ≈ os b → y ≈ y → Rel₊ b n1 y
    rc : ∀ {b c y x x′} → Rel₊ b x c → Rel₊ c x′ y → Rel₊ b (x ⨾ x′) y
    rb : ∀ {b b′ x y} → b′ ≈ b → b ≈ b → Rel₊ b x y → Rel₊ b′ x y
    rr : ∀ {b x y y′} → Rel₊ b x y → y ≈ y′ → y′ ≈ y′ → Rel₊ b x y′
    rl : ∀ {b y d} (g : ℕ → O L) → y ≈ ol g → y ≈ y → (∀ n → g n ≈ g n) → b ≈ g 0 →
         (∀ m → Rel₊ (g m) (d m) (g (suc m))) → Rel₊ b (nl d) y
    rd : ∀ {b y d} (g : ℕ → O L) → y ≈ ol g → y ≈ y → (∀ n → g n ≈ g n) → g 0 ⊴ g 1 →
         Rel₊ b (nl d) (ol (λ m → g (suc m))) → Rel₊ b (nl d) y
    ri : ∀ {b y k} (r′ : k ≪ L) (u : N.Ws L (≪S r′) → D L) (p : k ≪ L) (H : O k → O L) →
         y ≈ oi p (λ z → H (outS (≪S p) z)) → y ≈ y →
         b ≈ H (Ω̇ k) →
         ContF (λ s₁ → ≪≪ s₁ p) H →
         (∀ w z₀ z₁ → Lw (≪S r′) (Ω̇ k) w z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Rel₊ (H z₀) (u (N.inS (≪S r′) w)) (H z₁)) →
         Rel₊ b (ni r′ u) y

Rel : ∀ L → O L → D L → O L → Set
Rw  : ∀ L {a} → Strict a L → O a → D a → O a → Set
Rc  : ∀ b {a} → a ⊲ b → O a → D a → O a → Set
Rel L = Rel₊ L (Rw L)
Rw (asuc b) (ss P) = Rc b P
Rw (alim f) (sl n P) = Rc (f n) P
Rc a self = Rel a
Rc (asuc b) (suc P) = Rc b P
Rc (alim f) (lim n P) = Rc (f n) P

Rc→ : ∀ {b a} (P : a ⊲ b) {x y z} → Rc b P x y z → Rel a x y z
Rc→ self d = d
Rc→ (suc P) d = Rc→ P d
Rc→ (lim n P) d = Rc→ P d

→Rc : ∀ {b a} (P : a ⊲ b) {x y z} → Rel a x y z → Rc b P x y z
→Rc self d = d
→Rc (suc P) d = →Rc P d
→Rc (lim n P) d = →Rc P d

relR : ∀ {L b x y} → Rel L b x y → y ≈ y
relR (rz _ p) = p
relR (rs _ p) = p
relR (rc _ D) = relR D
relR (rb _ _ D) = relR D
relR (rr _ _ p) = p
relR (rl _ _ p _ _ _) = p
relR (rd _ _ p _ _ _) = p
relR (ri _ _ _ _ _ p _ _ _) = p

Rw→ : ∀ {L a} (R : Strict a L) {x y z} → Rw L R x y z → Rel a x y z
Rw→ (ss P) d = Rc→ P d
Rw→ (sl n P) d = Rc→ P d

→Rw : ∀ {L a} (R : Strict a L) {x y z} → Rel a x y z → Rw L R x y z
→Rw (ss P) d = →Rc P d
→Rw (sl n P) d = →Rc P d
```

## §3 换路径

把节点写成 $H\circ\mathrm{out}$. `≈-rp`: $x$ 等价于路径 $r$ 上分支 $F$ 的节点, 且 $F$ 在 $r$ 上就是 $G_0$, 那么它也等价于任何路径上 $G_0$ 的节点. 不用传递性.

```agda
≈-rp′  : ∀ {a L k} (x : O a) {r : k ≪ L} {L′ : A} {F : Vs L (≪S r) → O L} {G₀ : O k → O L′} {r″ : k ≪ L′} →
         x ≈ oi r F → (∀ {c} (x₀ : O c) (z : O k) → x₀ ≈ F (inS (≪S r) z) → x₀ ≈ G₀ z) → x ≈ oi r″ (λ y → G₀ (outS (≪S r″) y))
≈-rpS : ∀ {a₀ a L k} (R₀ : Strict a a₀) (x : Vs a₀ R₀) {r : k ≪ L} {L′ : A} {F : Vs L (≪S r) → O L} {G₀ : O k → O L′} {r″ : k ≪ L′} →
        EqL R₀ x (oi r F) → (∀ {c} (x₀ : O c) (z : O k) → x₀ ≈ F (inS (≪S r) z) → x₀ ≈ G₀ z) → EqL R₀ x (oi r″ (λ y → G₀ (outS (≪S r″) y)))
≈-rpC : ∀ {a₀ a L k} (R₀ : a ⊲ a₀) (x : Vc a₀ R₀) {r : k ≪ L} {L′ : A} {F : Vs L (≪S r) → O L} {G₀ : O k → O L′} {r″ : k ≪ L′} →
        EqLC R₀ x (oi r F) → (∀ {c} (x₀ : O c) (z : O k) → x₀ ≈ F (inS (≪S r) z) → x₀ ≈ G₀ z) → EqLC R₀ x (oi r″ (λ y → G₀ (outS (≪S r″) y)))

≈-rp′ (oi r₀ h) {r} {r″ = r″} (refl , p) q = ≈node refl λ y y′ d →
  q (h y) (outS (≪S r″) y′)
    (p y (inS (≪S r) (outS (≪S r″) y′)) (→V (≪S r₀) (≪S r) y _ (subst (λ v → outS (≪S r₀) y ≈ v) (sym (out-inS (≪S r) (outS (≪S r″) y′))) d)))
≈-rp′ (oe R₀ x) e q = ≈-rpS R₀ x e q
≈-rpS (ss P) x e q = ≈-rpC P x e q
≈-rpS (sl n P) x e q = ≈-rpC P x e q
≈-rpC self x e q = ≈-rp′ x e q
≈-rpC (suc P) x e q = ≈-rpC P x e q
≈-rpC (lim n P) x e q = ≈-rpC P x e q

≈-rp : ∀ {a L k} (x : O a) {r r′ : k ≪ L} {F : Vs L (≪S r) → O L} {G₀ : O k → O L} →
       x ≈ oi r F → (∀ z → F (inS (≪S r) z) ≡ G₀ z) → x ≈ oi r′ (λ y → G₀ (outS (≪S r′) y))
≈-rp x {r} {r′} {F} {G₀} e q = ≈-rp′ x {r} {r″ = r′} e (λ x₀ z d → subst (λ v → x₀ ≈ v) (q z) d)

-- ol, os 的右边换掉
≈-ol′ : ∀ {a L L′} (x : O a) {F : ℕ → O L} {G : ℕ → O L′} → x ≈ ol F → (∀ {c} (x₀ : O c) n → x₀ ≈ F n → x₀ ≈ G n) → x ≈ ol G
≈-olS : ∀ {a₀ a L L′} (R₀ : Strict a a₀) (x : Vs a₀ R₀) {F : ℕ → O L} {G : ℕ → O L′} → EqL R₀ x (ol F) → (∀ {c} (x₀ : O c) n → x₀ ≈ F n → x₀ ≈ G n) → EqL R₀ x (ol G)
≈-olC : ∀ {a₀ a L L′} (R₀ : a ⊲ a₀) (x : Vc a₀ R₀) {F : ℕ → O L} {G : ℕ → O L′} → EqLC R₀ x (ol F) → (∀ {c} (x₀ : O c) n → x₀ ≈ F n → x₀ ≈ G n) → EqLC R₀ x (ol G)
≈-ol′ (ol F₀) e q = λ n → q (F₀ n) n (e n)
≈-ol′ (oe R₀ x) e q = ≈-olS R₀ x e q
≈-olS (ss P) x e q = ≈-olC P x e q
≈-olS (sl n P) x e q = ≈-olC P x e q
≈-olC self x e q = ≈-ol′ x e q
≈-olC (suc P) x e q = ≈-olC P x e q
≈-olC (lim n P) x e q = ≈-olC P x e q

≈-ol : ∀ {a L} (x : O a) {F G : ℕ → O L} → x ≈ ol F → (∀ n → F n ≡ G n) → x ≈ ol G
≈-ol x e q = ≈-ol′ x e (λ x₀ n d → subst (λ v → x₀ ≈ v) (q n) d)

≈-os′ : ∀ {a L L′} (x : O a) {F : O L} {G : O L′} → x ≈ os F → (∀ {c} (x₀ : O c) → x₀ ≈ F → x₀ ≈ G) → x ≈ os G
≈-osS : ∀ {a₀ a L L′} (R₀ : Strict a a₀) (x : Vs a₀ R₀) {F : O L} {G : O L′} → EqL R₀ x (os F) → (∀ {c} (x₀ : O c) → x₀ ≈ F → x₀ ≈ G) → EqL R₀ x (os G)
≈-osC : ∀ {a₀ a L L′} (R₀ : a ⊲ a₀) (x : Vc a₀ R₀) {F : O L} {G : O L′} → EqLC R₀ x (os F) → (∀ {c} (x₀ : O c) → x₀ ≈ F → x₀ ≈ G) → EqLC R₀ x (os G)
≈-os′ (os F₀) e q = q F₀ e
≈-os′ (oe R₀ x) e q = ≈-osS R₀ x e q
≈-osS (ss P) x e q = ≈-osC P x e q
≈-osS (sl n P) x e q = ≈-osC P x e q
≈-osC self x e q = ≈-os′ x e q
≈-osC (suc P) x e q = ≈-osC P x e q
≈-osC (lim n P) x e q = ≈-osC P x e q
```

## §4 折叠的计算

```agda
ψ-keep : ∀ {t L k} (T : Tg t L) (w : Lg L) (p : k ≪ L) (G : O k → O L) (s₁ : k ≪ t) → rkT p T w ≡ keep s₁ →
         ψ t T w (oi p (λ y → G (outS (≪S p) y))) ≡ oi s₁ (λ y → ψ t T w (G (outS (≪S p) (inS (≪S p) (outS (≪S s₁) y)))))
ψ-keep T w p G s₁ e rewrite e = refl

ψ-rise : ∀ {t L k} (T : Tg t L) (w : Lg L) (p : k ≪ L) (G : O k → O L) (q : t ⊲ k) → rkT p T w ≡ rise q →
         ψ t T w (oi p (λ y → G (outS (≪S p) y))) ≡
         ol (λ n → ψ t T w (G (outS (≪S p) (inS (≪S p) (chainᵒ (λ z → ψ k (inj₁ (≪⊲ p)) w (G (outS (≪S p) (inS (≪S p) z)))) n)))))
ψ-rise T w p G q e rewrite e = refl

chain≡ : ∀ {k} {f g : O k → O k} → (∀ z → f z ≡ g z) → ∀ n → chainᵒ f n ≡ chainᵒ g n
chain≡ q zero = refl
chain≡ {f = f} {g} q (suc n) = trans (cong f (chain≡ q n)) (q (chainᵒ g n))
```

## §5 折叠保连续性

$H$ 连续, $k\ll t$, 那么 $\psi_t\circ H$ 连续.

```agda
ψ-ContF : ∀ {t M k} (T : Tg t M) (w : Lg M) (ks : k ≪ t) {κ : ∀ {j} → j ≪ k → j ≪ M} {H : O k → O M} → ContF κ H →
          ContF (λ s₁ → ≪≪ s₁ ks) (λ z → ψ t T w (H z))
ψ-ContF {t} T w ks {κ} {H} C = record
  { cq = λ e → ψQ _ _ T w T w (cq C e)
  ; cl = λ g e → ψQ _ _ T w T w (cl C g e)
  ; cn = cn′
  ; cm = λ d → ψL T w T w (cm C d)
  }
  where
  cn′ : ∀ {z j} (s₁ : j ≪ _) (g : O j → O _) → z ≈ oi s₁ (λ y → g (outS (≪S s₁) y)) → (∀ {a a′} → a ≈ a′ → g a ≈ g a′) →
        ψ t T w (H z) ≈ oi (≪≪ s₁ ks) (λ y → ψ t T w (H (g (outS (≪S (≪≪ s₁ ks)) y))))
  cn′ {z} {j} s₁ g e q with rkT (κ s₁) T w in eq
  ... | keep s₂ = ≈-rp (ψ t T w (H z)) {r = s₂} (subst (λ v → ψ t T w (H z) ≈ v) (ψ-keep T w (κ s₁) G s₂ eq) (ψQ _ _ T w T w (cn C s₁ g e q)))
         (λ a → cong (λ v → ψ t T w (G v)) (trans (out-inS (≪S (κ s₁)) _) (out-inS (≪S s₂) a)))
    where G = λ a → H (g a)
  ... | rise q₁ = ⊥-elim (no-keep-rise (≪≪ s₁ ks) q₁)
```

## §6 加法

```agda
add-ContF : ∀ {k L} {κ : ∀ {j} → j ≪ k → j ≪ L} {H : O k → O L} (B : O L) → B ≈ B → ContF κ H → ContF κ (λ z → B ⊕ H z)
add-ContF {κ = κ} {H} B e C = record
  { cq = λ {z} {z′} d → add≈ self self e (H z) (H z′) (cq C d)
  ; cl = λ {z} g d → add≈ self self e (H z) (ol (λ n → H (g n))) (cl C g d)
  ; cn = λ {z} s₁ g d q → ≈-rp (B ⊕ H z) {r = κ s₁}
           (add≈ self self e (H z) (oi (κ s₁) (λ y → H (g (outS (≪S (κ s₁)) y)))) (cn C s₁ g d q))
           (λ a → cong (λ v → B ⊕ H (g v)) (trans (out-inS (≪S (κ s₁)) _) (out-inS (≪S (κ s₁)) a)))
  ; cm = λ d → add-mono self self e (cm C d)
  }

add-Rel : ∀ {L} (B : O L) → B ≈ B → ∀ {b x y} → Rel L b x y → Rel L (B ⊕ b) x (B ⊕ y)
add-Rel B e {b} {y = y} (rz d p) = rz (add≈ self self e b y d) (add≈ self self e y y p)
add-Rel B e {b} {y = y} (rs d p) = rs (add≈ self self e y (os b) d) (add≈ self self e y y p)
add-Rel B e (rc D₁ D₂) = rc (add-Rel B e D₁) (add-Rel B e D₂)
add-Rel B e {b} (rb {b = b₁} d p D) = rb (add≈ self self e b b₁ d) (add≈ self self e b₁ b₁ p) (add-Rel B e D)
add-Rel B e {y = y′} (rr {y = y} D d p) = rr (add-Rel B e D) (add≈ self self e y y′ d) (add≈ self self e y′ y′ p)
add-Rel B e {b} {y = y} (rl g d p q e₀ st) =
  rl (λ n → B ⊕ g n) (add≈ self self e y (ol g) d) (add≈ self self e y y p) (λ n → add≈ self self e (g n) (g n) (q n))
     (add≈ self self e b (g 0) e₀) (λ m → add-Rel B e (st m))
add-Rel B e {y = y} (rd g d p q f D) =
  rd (λ n → B ⊕ g n) (add≈ self self e y (ol g) d) (add≈ self self e y y p) (λ n → add≈ self self e (g n) (g n) (q n))
     (add-mono self self e f) (add-Rel B e D)
add-Rel B e {b} {y = y} (ri {k = k} r′ u p₀ H d p e₀ C ds) =
  ri r′ u p₀ (λ z → B ⊕ H z)
     (≈-rp (B ⊕ y) {r = p₀} (add≈ self self e y (oi p₀ (λ z → H (outS (≪S p₀) z))) d)
        (λ a → cong (λ v → B ⊕ H v) (trans (out-inS (≪S p₀) _) (out-inS (≪S p₀) a))))
     (add≈ self self e y y p)
     (add≈ self self e b (H (Ω̇ k)) e₀)
     (add-ContF B e C)
     (λ w z₀ z₁ c d′ p′ → add-Rel B e (ds w z₀ z₁ c d′ p′))
```

## §7 $\Omega$

`emb`: 低层的旧树懒嵌入. `≈` 透明.

```agda
emb : ∀ {a L} → a ⊲ L → O a → O L
emb self x = x
emb (suc P) x = oe (ss P) (inC P x)
emb (lim n P) x = oe (sl n P) (inC P x)

emb≈ˡ : ∀ {a L c} (q : a ⊲ L) {x : O a} {y : O c} → x ≈ y → emb q x ≈ y
emb≈ˡ self d = d
emb≈ˡ (suc P) {x} {y} d = →L (ss P) (inC P x) (subst (λ v → v ≈ y) (sym (out-inC P x)) d)
emb≈ˡ {L = alim f} (lim n P) {x} {y} d = →L (sl {f = f} n P) (inC P x) (subst (λ v → v ≈ y) (sym (out-inC P x)) d)

emb≈ʳ : ∀ {a L c} (q : a ⊲ L) {x : O c} {y : O a} → x ≈ y → x ≈ emb q y
emb≈ʳ self d = d
emb≈ʳ (suc P) {x} {y} d = ≈oe x (ss P) (inC P y) (subst (λ v → x ≈ v) (sym (out-inC P y)) d)
emb≈ʳ {L = alim f} (lim n P) {x} {y} d = ≈oe x (sl {f = f} n P) (inC P y) (subst (λ v → x ≈ v) (sym (out-inC P y)) d)

emb≈ : ∀ {a b L L′} (q : a ⊲ L) (q′ : b ⊲ L′) {x : O a} {y : O b} → x ≈ y → emb q x ≈ emb q′ y
emb≈ q q′ d = emb≈ˡ q (emb≈ʳ q′ d)

emb⊴ʳ : ∀ {a L c} (q : a ⊲ L) {x : O c} {y : O a} → x ⊴ y → x ⊴ emb q y
emb⊴ʳ self d = d
emb⊴ʳ (suc P) {x} {y} d = eR {R = ss P} (subst (λ v → x ⊴ v) (sym (out-inC P y)) d)
emb⊴ʳ {L = alim f} (lim n P) {x} {y} d = eR {R = sl {f = f} n P} (subst (λ v → x ⊴ v) (sym (out-inC P y)) d)

emb⊴ˡ : ∀ {a L c} (q : a ⊲ L) {x : O a} {y : O c} → x ⊴ y → emb q x ⊴ y
emb⊴ˡ self d = d
emb⊴ˡ (suc P) {x} {y} d = eL {R = ss P} (subst (λ v → v ⊴ y) (sym (out-inC P x)) d)
emb⊴ˡ {L = alim f} (lim n P) {x} {y} d = eL {R = sl {f = f} n P} (subst (λ v → v ⊴ y) (sym (out-inC P x)) d)

-- 节点上的恒等分支: 走第一个节点就是嵌入
idH : ∀ {c L} (r : c ≪ L) → O c → O L
idH r z = oe (≪S r) (inS (≪S r) z)

idH≈ˡ : ∀ {c L d} (r : c ≪ L) {x : O c} {y : O d} → x ≈ y → idH r x ≈ y
idH≈ˡ r {x} {y} e = →L (≪S r) (inS (≪S r) x) (subst (λ v → v ≈ y) (sym (out-inS (≪S r) x)) e)

idH≈ʳ : ∀ {c L d} (r : c ≪ L) {x : O d} {y : O c} → x ≈ y → x ≈ idH r y
idH≈ʳ r {x} {y} e = ≈oe x (≪S r) (inS (≪S r) y) (subst (λ v → x ≈ v) (sym (out-inS (≪S r) y)) e)

idH-ContF : ∀ {c L} (r : c ≪ L) → ContF (λ s₁ → ≪≪ s₁ r) (idH r)
idH-ContF {c} {L} r = record
  { cq = λ e → idH≈ˡ r (idH≈ʳ r e)
  ; cl = λ g e → idH≈ˡ r (≈-ol′ _ e (λ x₀ n d → idH≈ʳ r d))
  ; cn = λ s₁ g e q → idH≈ˡ r (≈-rp′ _ e (λ x₀ z d → idH≈ʳ r (subst (λ v → x₀ ≈ v) (cong g (out-inS (≪S s₁) z)) d)))
  ; cm = λ {z} {z′} d → eL {R = ≪S r} (subst (λ v → v ⊴ idH r z′) (sym (out-inS (≪S r) z)) (eR {R = ≪S r} (subst (λ v → z ⊴ v) (sym (out-inS (≪S r) z′)) d)))
  }
```

```agda
drpn : ∀ {L b d} (n : ℕ) (G : ℕ → O L) {y : O L} → y ≈ ol G → y ≈ y → (∀ i → G i ≈ G i) → (∀ i → G i ⊴ G (suc i)) → b ≈ G n →
       (∀ m → Rel L (G (m + n)) (d m) (G (suc (m + n)))) → Rel L b (nl d) y
drpn {L} {d = d} zero G e p q h e₀ st = rl G e p q e₀ (λ m → subst (λ i → Rel L (G i) (d m) (G (suc i))) (+-identityʳ m) (st m))
drpn {L} {d = d} (suc n) G e p q h e₀ st =
  rd G e p q (h 0) (drpn n (λ i → G (suc i)) (λ i → q (suc i)) (λ i → q (suc i)) (λ i → q (suc i)) (λ i → h (suc i)) e₀
    (λ m → subst (λ i → Rel L (G i) (d m) (G (suc i))) (+-suc m n) (st m)))

Dif-Rel : ∀ b {a L} (p : a ⊲ b) (q : b ⊲ L) (w : Lg b) → Rel L (emb (⊲-tr p q) (Ω̇ a)) (Dif b p q w) (emb q (Ω̇ b))
Dif-Rel b self q w = rz (emb≈ (⊲-tr self q) q (Ω≈ b)) (emb≈ q q (Ω≈ b))
Dif-Rel (asuc c) {a} {L} (suc p) q w =
  rc (rb (emb≈ (⊲-tr (suc p) q) (⊲-tr p (⊲-tr (suc self) q)) (Ω≈ a)) (emb≈ (⊲-tr p (⊲-tr (suc self) q)) (⊲-tr p (⊲-tr (suc self) q)) (Ω≈ a)) (Dif-Rel c p (⊲-tr (suc self) q) w))
     (ri r′ (λ _ → n1) r′ (idH r′)
        (emb≈ˡ q (≈-rp′ (Ω̇ (asuc c)) {r = zero} {r″ = r′} (Ω≈ (asuc c))
           (λ x₀ z d → idH≈ʳ r′ (oe≈ x₀ (ss self) z d))))
        (emb≈ q q (Ω≈ (asuc c)))
        (emb≈ˡ (⊲-tr (suc self) q) (idH≈ʳ r′ (Ω≈ c)))
        (idH-ContF r′)
        (λ w₁ z₀ z₁ h d p → rs (idH≈ˡ r′ (≈-os′ z₁ d (λ x₀ e → idH≈ʳ r′ e))) (idH≈ˡ r′ (idH≈ʳ r′ p))))
  where
  r′ = ≪∘ zero q
Dif-Rel (alim f) {a} {L} (lim n p) q (st , w) =
  rc (rb (emb≈ (⊲-tr (lim n p) q) (⊲-tr p (qq n)) (Ω≈ a)) (emb≈ (⊲-tr p (qq n)) (⊲-tr p (qq n)) (Ω≈ a)) (Dif-Rel (f n) p (qq n) (w n)))
     (drpn n G (emb≈ˡ q (λ m → emb≈ʳ (qq m) (Ω≈ (f m)))) (emb≈ q q (Ω≈ (alim f))) (λ i → emb≈ (qq i) (qq i) (Ω≈ (f i)))
        (λ i → emb⊴ˡ (qq i) (emb⊴ʳ (qq (suc i)) (Ω⊴ (st i)))) (emb≈ (qq n) (qq n) (Ω≈ (f n)))
        (λ m → rb (emb≈ (qq (m + n)) (⊲-tr (st (m + n)) (qq (suc (m + n)))) (Ω≈ (f (m + n)))) (emb≈ (⊲-tr (st (m + n)) (qq (suc (m + n)))) (⊲-tr (st (m + n)) (qq (suc (m + n)))) (Ω≈ (f (m + n))))
                  (Dif-Rel (f (suc (m + n))) (st (m + n)) (qq (suc (m + n))) (w (suc (m + n))))))
  where
  qq : ∀ m → f m ⊲ L
  qq m = ⊲-tr (lim m self) q
  G : ℕ → O L
  G m = emb (qq m) (Ω̇ (f m))

Ω-Rel : ∀ a {L} (q : a ⊲ L) (w : Lg a) → Rel L o0 (Ωd a q w) (emb q (Ω̇ a))
Ω-Rel a q w = rc (rs (emb≈ˡ (⊲-tr (z⊲ a) q) tt) (emb≈ (⊲-tr (z⊲ a) q) (⊲-tr (z⊲ a) q) tt)) (Dif-Rel a (z⊲ a) q w)
```

## §8 积分

`Int`: 分支上走过 $\delta$. 对应就是分支本身走过的路.

```agda
ContF-κ : ∀ {k M} {κ κ′ : ∀ {j} → j ≪ k → j ≪ M} {H : O k → O M} → ContF κ H → ContF κ′ H
ContF-κ {κ = κ} {κ′} {H} C = record
  { cq = cq C
  ; cl = cl C
  ; cn = λ {z} s₁ g e q → ≈-rp (H z) {r = κ s₁} (cn C s₁ g e q) (λ a → cong (λ v → H (g v)) (out-inS (≪S (κ s₁)) a))
  ; cm = cm C
  }

Ipt-Rel : ∀ {j k} (ac : AccL j) (r : j ≪ k) (u : D j → D k) {w : D j} {z₀ : O j} {d : ℕ → D j} (g : ℕ → O j) →
          Rel j (Ω̇ j) w z₀ → z₀ ≈ g 0 → (∀ n → g n ≈ g n) → (∀ m → Rel j (g m) (d m) (g (suc m))) → ∀ m → Rel j (Ω̇ j) (Ipt ac r u w d m) (g m)
Ipt-Rel ac r u g c e p st zero = rr c e (p 0)
Ipt-Rel ac r u g c e p st (suc m) = rc (Ipt-Rel ac r u g c e p st m) (st m)

IntRel : ∀ {j k} (ac : AccL j) (r′ : j ≪ k) {κ : ∀ {i} → i ≪ j → i ≪ k} {H : O j → O k} (u : D j → D k) → ContF κ H →
         (∀ w z₀ z₁ → Rel j (Ω̇ j) w z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Rel k (H z₀) (u w) (H z₁)) →
         ∀ {w z₀ δ z₁} → Rel j (Ω̇ j) w z₀ → Rel j z₀ δ z₁ → Rel k (H z₀) (Int ac r′ u w δ) (H z₁)
IntRel ac r′ u C ds c (rz e p) = rz (cq C e) (cq C p)
IntRel ac r′ u C ds c (rs e p) = ds _ _ _ c e p
IntRel ac r′ u C ds c (rc D₁ D₂) = rc (IntRel ac r′ u C ds c D₁) (IntRel ac r′ u C ds (rc c D₁) D₂)
IntRel ac r′ u C ds c (rb e p D) = rb (cq C e) (cq C p) (IntRel ac r′ u C ds (rr c e p) D)
IntRel ac r′ u C ds c (rr D e p) = rr (IntRel ac r′ u C ds c D) (cq C e) (cq C p)
IntRel ac r′ {H = H} u C ds c (rl g e p q e₀ st) =
  rl (λ n → H (g n)) (cl C g e) (cq C p) (λ n → cq C (q n)) (cq C e₀)
     (λ m → IntRel ac r′ u C ds (Ipt-Rel ac r′ u g c e₀ q st m) (st m))
IntRel ac r′ {H = H} u C ds c (rd g e p q f D) =
  rd (λ n → H (g n)) (cl C g e) (cq C p) (λ n → cq C (q n)) (cm C f)
     (rr (IntRel ac r′ u C ds c D) (cl C (λ m → g (suc m)) (λ n → q (suc n))) (λ n → cq C (q (suc n))))
IntRel {j} {k} (acc f) r′ {κ} {H} u C ds {w = w} c (ri {k = i} r₃ v p₂ H₂ e p e₀ C₂ ds₂) =
  ri (≪≪ r₃ r′) _ (κ p₂) (λ z → H (H₂ z))
     (cn C p₂ H₂ e (cq C₂))
     (cq C p)
     (cq C e₀)
     (ContF-κ (comp C₂ C))
     (λ w₂ a₀ a₁ h d pz → subst (λ z → Rel k (H (H₂ a₀)) (Int (acc f) r′ u (w ⨾ Int (f r₃) r₃ v₁ n0 z) (v (N.inS (≪S r₃) z))) (H (H₂ a₁)))
        (sym (N.out-inS (≪S (≪≪ r₃ r′)) w₂))
        (IntRel (acc f) r′ u C ds
           (rc c (rb e₀ (cq C₂ (Ω≈ i)) (IntRel (f r₃) r₃ v₁ C₂ (λ w₁ z₀ z₁ c₁ d₁ p₁ → ds₂ w₁ z₀ z₁ (→Rw (≪S r₃) c₁) d₁ p₁) (rz (Ω≈ i) (Ω≈ i)) (Rw→ (≪S (≪≪ r₃ r′)) h))))
           (ds₂ w₂ a₀ a₁ (→Rw (≪S r₃) (Rw→ (≪S (≪≪ r₃ r′)) h)) d pz)))
  where
  v₁ = λ z′ → v (N.inS (≪S r₃) z′)
```
