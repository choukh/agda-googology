# 右边放宽的底关系
不读记号；工具。关系 `N`：`YiVRRel.LeS` 的规则加右规则 `≼W`（槽位结点在入口分支 z 处进入：z 不高于一切第一位置不低于该槽位层 Ω 树的树，左边在 z 之上的一切分支之下）；分支、孩子、入口条件按层号遗传。各行照 `YiVRRel`、`YiKAMono.le◃`、`YiOGRelPeel.right-add` 搬来，多 `≼W` 一行。
编译定理：`N` 推出值序（`sound`，前提 `Ser` 是分支关系处处有上界，只用于 `w≼w`；`≼W` 一行用入口条件自带的见证；第 0、1 层无条件 `ser₀`、`ser₁`）；加法、`next⁺`、部分和极限、嵌入、上折保持 `N`；不含 Ω 形状的层号的 Ω 树在规范域且可作入口（`Ωt≼`、`entry`）。
不否定什么；实例在 [YiRRPair](YiRRPair.lagda.md)，折叠在 [YiRRFold](YiRRFold.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiVWVal as V
open import OCF.Lean.YiVRRel using (NoΩ)
open import OCF.Lean.YiLXClimb using (_⊴◃_)
```

## 一层之内与各层

```agda
data NS (S : Sg) (RB : (p : P S) → B S p → B S p → Set) (RD : (c : C S) → D S c → D S c → Set)
        (EB : (p : P S) → B S p → Set) : T S → T S → Set where
  z≼  : ∀ {b} → NS S RB RD EB zero b
  s≼s : ∀ {a b} → NS S RB RD EB a b → NS S RB RD EB (suc a) (suc b)
  ≼s  : ∀ {a b} → NS S RB RD EB a b → NS S RB RD EB a (suc b)
  ≼l  : ∀ {a f r} (n : ℕ) → NS S RB RD EB a (f n) → NS S RB RD EB a (lim f r)
  l≼  : ∀ {f r b} → ((n : ℕ) → NS S RB RD EB (f n) b) → NS S RB RD EB (lim f r) b
  ≼w  : ∀ {a p g} → NS S RB RD EB a (g (b₀ S p)) → NS S RB RD EB a (Ω p g)
  w≼w : ∀ {p g g′} → ((z z′ : B S p) → RB p z z′ → NS S RB RD EB (g z) (g′ z′)) → NS S RB RD EB (Ω p g) (Ω p g′)
  ≼W  : ∀ {a p g} (z : B S p) → EB p z → ((z′ : B S p) → RB p z z′ → NS S RB RD EB a (g z′)) → NS S RB RD EB a (Ω p g)
  ≼u  : ∀ {a x c y e} → NS S RB RD EB a x → NS S RB RD EB a (up x c y e)
  u≼u : ∀ {x x′ c y y′ e e′} → NS S RB RD EB x x′ → RD c y y′ → NS S RB RD EB (up x c y e) (up x′ c y′ e′)

mutual
  NB : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Br ℓ p → Set
  NB (nd s h)      (inj₂ (c , t)) = NB⁼ (h c) t
  NB (nd (sΩ k) h) (inj₁ t)       = NB⁼ k t

  NB⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Br⁼ a t → Set
  NB⁼ a (inj₁ _) = NS (Sig a) (NB a) (NC a) (NE a)
  NB⁼ a (inj₂ p) = NB a p

  NC : (ℓ : L) (c : CH ℓ) → ChT ℓ c → ChT ℓ c → Set
  NC (nd s h) c = NS (Sig (h c)) (NB (h c)) (NC (h c)) (NE (h c))

  NE : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Set
  NE ℓ p z = (y : Tr (at ℓ p)) → proj₁ (Ωt (at ℓ p)) ⊴◃ y → NB ℓ p z (fromBr ℓ p y)

NE⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Set
NE⁼ a t z = (y : Tr (proj₁ (sl⁼ a t))) → proj₁ (Ωt (proj₁ (sl⁼ a t))) ⊴◃ y → NB⁼ a t z (proj₂ (sl⁼ a t) y)

N : (ℓ : L) → Tr ℓ → Tr ℓ → Set
N ℓ = NS (Sig ℓ) (NB ℓ) (NC ℓ) (NE ℓ)
```

## 推出值序

`Ser ℓ`: 每个槽位上的分支关系处处有上界, 孩子层同样. 只有 `w≼w` 一行要它; `≼W` 一行取入口条件在该层 Ω 树处的见证.

```agda
Ser : L → Set
Ser zero     = ⊤
Ser (nd s h) = ((p : Pos (nd s h)) (z : Br (nd s h) p) → Σ (Br (nd s h) p) (NB (nd s h) p z)) × ((c : Ch s) → Ser (h c))

sound : (ℓ : L) → Ser ℓ → {x y : Tr ℓ} → N ℓ x y → V.val ℓ x V.≼ V.val ℓ y
sound ℓ σ z≼ = V.z≼
sound ℓ σ (s≼s d) = V.s≼s (sound ℓ σ d)
sound ℓ σ (≼s d) = V.≼-suc (sound ℓ σ d)
sound ℓ σ (≼l n d) = V.≼l n (sound ℓ σ d)
sound ℓ σ (l≼ h) = V.l≼ (λ n → sound ℓ σ (h n))
sound ℓ σ (≼w d) = V.≼Ω _ (sound ℓ σ d)
sound zero σ (w≼w {p = ()} h)
sound (nd s h) σ (w≼w {p = p} k) =
  V.Ω≼ (λ z → V.≼Ω (proj₁ (proj₁ σ p z)) (sound (nd s h) σ (k z _ (proj₂ (proj₁ σ p z)))))
sound zero σ (≼W {p = ()} z ez k)
sound (nd s h) σ (≼W {p = p} z ez k) =
  V.≼Ω (fromBr (nd s h) p (proj₁ (Ωt (at (nd s h) p)))) (sound (nd s h) σ (k _ (ez _ (inj₁ refl))))
sound zero σ (≼u {c = ()} d)
sound (nd s h) σ (≼u {x = x} {c = c} {y = y} d) =
  V.≼-trans (sound (nd s h) σ d) (V.≼⊹ (V.val (nd s h) x) (V.valCh (nd s h) c y))
sound zero σ (u≼u {c = ()} dx dy)
sound (nd s h) σ (u≼u {x = x} {x′ = x′} {c = c} {y = y} dx dy) =
  V.≼-trans (V.⊹-monoˡ (sound (nd s h) σ dx) (V.valCh (nd s h) c y))
            (V.⊹-mono (V.val (nd s h) x′) (V.emb-mono (nd s h) c (sound (h c) (proj₂ σ c) dy)))

nrefl₀ : (x : Tr zero) → N zero x x
nrefl₀ zero      = z≼
nrefl₀ (suc x)   = s≼s (nrefl₀ x)
nrefl₀ (lim f a) = l≼ (λ n → ≼l n (nrefl₀ (f n)))

L1 : L
L1 = nd sS (λ _ → zero)

ser₀ : Ser zero
ser₀ = tt

ser₁ : Ser L1
ser₁ = (λ { (inj₂ (tt , inj₁ tt)) z → z , nrefl₀ z ; (inj₂ (tt , inj₂ ())) z }) , λ _ → tt

sound₁ : {x y : Tr L1} → N L1 x y → V.val L1 x V.≼ V.val L1 y
sound₁ = sound L1 ser₁
```

## 加法, next⁺, 部分和极限, 右加

```agda
module _ {S : Sg} {RB : (p : P S) → B S p → B S p → Set} {RD : (c : C S) → D S c → D S c → Set}
         {EB : (p : P S) → B S p → Set} where
  private
    _≼_ : T S → T S → Set
    _≼_ = NS S RB RD EB

  ≼+ : ∀ {a b} → a ≼ b → (c : T S) → a ≼ (b + c)
  ≼+ d zero         = d
  ≼+ d (suc c)      = ≼s (≼+ d c)
  ≼+ d (lim f r)    = ≼l 0 (≼+ d (f 0))
  ≼+ d (Ω p g)      = ≼w (≼+ d (g (b₀ S p)))
  ≼+ d (up y c w e) = ≼u (≼+ d y)

  +≼ : ∀ {a a′ c c′} → a ≼ a′ → c ≼ c′ → (a + c) ≼ (a′ + c′)
  +≼ {c′ = c′} da z≼ = ≼+ da c′
  +≼ da (s≼s d)    = s≼s (+≼ da d)
  +≼ da (≼s d)     = ≼s (+≼ da d)
  +≼ da (≼l n d)   = ≼l n (+≼ da d)
  +≼ da (l≼ h)     = l≼ (λ n → +≼ da (h n))
  +≼ da (≼w d)     = ≼w (+≼ da d)
  +≼ da (w≼w h)    = w≼w (λ z z′ r → +≼ da (h z z′ r))
  +≼ da (≼W z e h) = ≼W z e (λ z′ r → +≼ da (h z′ r))
  +≼ da (≼u d)     = ≼u (+≼ da d)
  +≼ da (u≼u d r)  = u≼u (+≼ da d) r

  right-add : ∀ {x y} → x ≼ y → (p : T S) → x ≼ (p + y)
  right-add z≼ p = z≼
  right-add (s≼s d) p = s≼s (right-add d p)
  right-add (≼s d) p = ≼s (right-add d p)
  right-add (≼l n d) p = ≼l n (right-add d p)
  right-add (l≼ h) p = l≼ (λ n → right-add (h n) p)
  right-add (≼w d) p = ≼w (right-add d p)
  right-add (w≼w h) p = w≼w (λ z z′ r → right-add (h z z′ r) p)
  right-add (≼W z e h) p = ≼W z e (λ z′ r → right-add (h z′ r) p)
  right-add (≼u d) p = ≼u (right-add d p)
  right-add (u≼u dx dy) p = u≼u (right-add dx p) dy

  iter≼ : ∀ {b b′} → b ≼ b′ → (n : ℕ) → iter (b +_) b n ≼ iter (b′ +_) b′ n
  iter≼ d zero    = d
  iter≼ d (suc n) = +≼ d (iter≼ d n)

  next≼ : (b b′ : T⁺ {S}) → proj₁ b ≼ proj₁ b′ → proj₁ (next⁺ b) ≼ proj₁ (next⁺ b′)
  next≼ b b′ d = l≼ (λ n → ≼l n (iter≼ d n))

  cum≼ : (F F′ : ℕ → T S) → ((n : ℕ) → F n ≼ F′ n) → (n : ℕ) → cum F n ≼ cum F′ n
  cum≼ F F′ h zero    = h zero
  cum≼ F F′ h (suc n) = +≼ (cum≼ F F′ h n) (h (suc n))

  limc≼ : (F F′ : ℕ → T⁺ {S}) → ((n : ℕ) → proj₁ (F n) ≼ proj₁ (F′ n)) → proj₁ (limc⁺ F) ≼ proj₁ (limc⁺ F′)
  limc≼ F F′ h = l≼ (λ n → ≼l n (cum≼ _ _ h n))
```

## Ω 树, 右接第一位置序, 入口

```agda
upz≼ : ∀ {s h} (c : Ch s) {y y′ : Tr⁺ (h c)} → N (h c) (proj₁ y) (proj₁ y′)
     → N (nd s h) (proj₁ (upz {s} {h} c y)) (proj₁ (upz {s} {h} c y′))
upz≼ c d = u≼u z≼ d

Ωt≼ : (ℓ : L) → NoΩ ℓ → N ℓ (proj₁ (Ωt ℓ)) (proj₁ (Ωt ℓ))
Ωt≼ zero          _ = s≼s z≼
Ωt≼ (nd sS h)     _ = w≼w (λ z z′ r → u≼u z≼ (s≼s r))
Ωt≼ (nd sL g)     ν = limc≼ (λ n → upz {sL} {g} n (Ωt (g n))) (λ n → upz {sL} {g} n (Ωt (g n)))
                            (λ n → upz≼ {sL} {g} n (Ωt≼ (g n) (ν n)))

le◃ : ∀ {ℓ} {a b c : Tr ℓ} → N ℓ a b → ℓ ⊢ b ◃ c → N ℓ a c
le◃ d ◃s           = ≼s d
le◃ d (◃l n)       = ≼l n d
le◃ d ◃w           = ≼w d
le◃ d (◃u x c y e) = ≼u d
le◃ {nd s h} z≼          (◃c x c r) = z≼
le◃ {nd s h} (l≼ k)      (◃c x c r) = l≼ (λ n → le◃ (k n) (◃c x c r))
le◃ {nd s h} (≼u d)      (◃c x c r) = ≼u d
le◃ {nd s h} (u≼u dx dy) (◃c x c r) = u≼u dx (le◃ {h c} dy r)
le◃ d (◃t e f) = le◃ (le◃ d e) f

le⊴ : ∀ {ℓ} {a b c : Tr ℓ} → N ℓ a b → b ⊴◃ c → N ℓ a c
le⊴ d (inj₁ refl) = d
le⊴ d (inj₂ e)    = le◃ d e

entry : (ℓ : L) → NoΩ ℓ → (y : Tr ℓ) → proj₁ (Ωt ℓ) ⊴◃ y → N ℓ (proj₁ (Ωt ℓ)) y
entry ℓ ν y e = le⊴ (Ωt≼ ℓ ν) e
```

## 换型: 槽位换层的分支关系与入口条件

`fromBr`, 上折的下行链 `mv`, 下标层的推进 `psh` 都只是换型; 逆向的 `mvBr⁻`, `pshBr⁻` 也是恒等.

```agda
mutual
  fromN : (ℓ : L) (p : Pos ℓ) {a b : Tr (at ℓ p)} → N (at ℓ p) a b → NB ℓ p (fromBr ℓ p a) (fromBr ℓ p b)
  fromN (nd s h)      (inj₂ (c , t)) d = fromN⁼ (h c) t d
  fromN (nd (sΩ k) h) (inj₁ t)       d = fromN⁼ k t d

  fromN⁼ : (a : L) (t : Pos⁼ a) {x y : Tr (proj₁ (sl⁼ a t))} → N (proj₁ (sl⁼ a t)) x y
         → NB⁼ a t (proj₂ (sl⁼ a t) x) (proj₂ (sl⁼ a t) y)
  fromN⁼ a (inj₁ _) d = d
  fromN⁼ a (inj₂ p) d = fromN a p d

mvBr⁻ : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → Br j p → Br ℓ (mv d p)
mvBr⁻ stop       p z = z
mvBr⁻ (down d c) p z = mvBr⁻ d (inj₂ (c , inj₂ p)) z

mvN : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) {z z′ : Br ℓ (mv d p)} → NB ℓ (mv d p) z z′ → NB j p (mvBr d p z) (mvBr d p z′)
mvN stop       p r = r
mvN (down d c) p r = mvN d (inj₂ (c , inj₂ p)) r

mvN⁻ : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) {z : Br j p} {z′ : Br ℓ (mv d p)}
     → NB ℓ (mv d p) (mvBr⁻ d p z) z′ → NB j p z (mvBr d p z′)
mvN⁻ stop       p r = r
mvN⁻ (down d c) p r = mvN⁻ d (inj₂ (c , inj₂ p)) r

mvE : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) {z : Br j p} → NE j p z → NE ℓ (mv d p) (mvBr⁻ d p z)
mvE stop       p e = e
mvE (down d c) p e = mvE d (inj₂ (c , inj₂ p)) e

pshBr⁻ : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → Br⁼ k t → Br⁼ a (psh v t)
pshBr⁻ self                 t z = z
pshBr⁻ (inc c v)            t z = pshBr⁻ v t z
pshBr⁻ {a = nd s h} (inu vs) t z = pshBr⁻ (vs (c₀ s)) t z
pshBr⁻ (ink v)              t z = pshBr⁻ v t z

pshN : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) {z z′ : Br⁼ a (psh v t)} → NB⁼ a (psh v t) z z′ → NB⁼ k t (pshBr v t z) (pshBr v t z′)
pshN self                  t r = r
pshN (inc c v)             t r = pshN v t r
pshN {a = nd s h} (inu vs) t r = pshN (vs (c₀ s)) t r
pshN (ink v)               t r = pshN v t r

pshN⁻ : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) {z : Br⁼ k t} {z′ : Br⁼ a (psh v t)}
      → NB⁼ a (psh v t) (pshBr⁻ v t z) z′ → NB⁼ k t z (pshBr v t z′)
pshN⁻ self                  t r = r
pshN⁻ (inc c v)             t r = pshN⁻ v t r
pshN⁻ {a = nd s h} (inu vs) t r = pshN⁻ (vs (c₀ s)) t r
pshN⁻ (ink v)               t r = pshN⁻ v t r

pshE : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) {z : Br⁼ k t} → NE⁼ k t z → NE⁼ a (psh v t) (pshBr⁻ v t z)
pshE self                  t e = e
pshE (inc c v)             t e = pshE v t e
pshE {a = nd s h} (inu vs) t e = pshE (vs (c₀ s)) t e
pshE (ink v)               t e = pshE v t e
```

## 嵌入与上折

```agda
emb≼ : (ℓ : L) (o : Ok ℓ) {k : L} (v : k ≤ ℓ) {y y′ : Tr⁺ k} → N k (proj₁ y) (proj₁ y′)
     → N ℓ (proj₁ (emb ℓ o v y)) (proj₁ (emb ℓ o v y′))
emb≼ ℓ             o self      d = d
emb≼ (nd s h)      o (inc c v) d = u≼u z≼ (emb≼ (h c) (proj₂ o c) v d)
emb≼ (nd s h)      o (inu vs)  d = u≼u z≼ (emb≼ (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) d)
emb≼ (nd (sΩ k) h) o (ink v)   d = u≼u z≼ (emb≼ (h zero) (proj₂ o zero) (v ∙ proj₂ (proj₁ o) zero) d)

≼Up : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr⁺ ℓ) (y : Tr j) {a : Tr ℓ} → N ℓ a (proj₁ b) → N ℓ a (proj₁ (Up j d b y))
≼Up j d b zero      e = e
≼Up j d b (suc y)   e = ≼l 0 (≼Up j d b y e)
≼Up j d b (lim f r) e = ≼l 0 (≼Up j d b (f 0) e)
≼Up {ℓ} j d b (Ω p g) {a} e =
  ≼w (subst (λ t → N ℓ a (proj₁ (Up j d b (g t)))) (sym (mvFirst d p)) (≼Up j d b (g (fromBr j p zero)) e))
≼Up (nd s h) d b (up y c y′ _) e = ≼Up (h c) (down d c) (Up (nd s h) d b y) y′ (≼Up (nd s h) d b y e)

Up≼ : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b b′ : Tr⁺ ℓ) → N ℓ (proj₁ b) (proj₁ b′) → {y y′ : Tr j} → N j y y′
    → N ℓ (proj₁ (Up j d b y)) (proj₁ (Up j d b′ y′))
Up≼ j d b b′ e {y′ = y′} z≼ = ≼Up j d b′ y′ e
Up≼ j d b b′ e (s≼s q)  = next≼ _ _ (Up≼ j d b b′ e q)
Up≼ j d b b′ e (≼s q)   = ≼l 0 (Up≼ j d b b′ e q)
Up≼ j d b b′ e (≼l n q) = ≼l n (Up≼ j d b b′ e q)
Up≼ j d b b′ e (l≼ h)   = l≼ (λ n → Up≼ j d b b′ e (h n))
Up≼ {ℓ} j d b b′ e {y = y} (≼w {p = p} {g = g} q) =
  ≼w (subst (λ t → N ℓ (proj₁ (Up j d b y)) (proj₁ (Up j d b′ (g t)))) (sym (mvFirst d p)) (Up≼ j d b b′ e q))
Up≼ j d b b′ e (w≼w {p = p} h) = w≼w (λ z z′ r → Up≼ j d b b′ e (h _ _ (mvN d p r)))
Up≼ j d b b′ e (≼W {p = p} z ez k) = ≼W (mvBr⁻ d p z) (mvE d p ez) (λ z′ r → Up≼ j d b b′ e (k _ (mvN⁻ d p r)))
Up≼ (nd s h) d b b′ e (≼u {x = x} {c = c} {y = y₁} q) =
  ≼Up (h c) (down d c) (Up (nd s h) d b′ x) y₁ (Up≼ (nd s h) d b b′ e q)
Up≼ (nd s h) d b b′ e (u≼u {c = c} q r) = Up≼ (h c) (down d c) _ _ (Up≼ (nd s h) d b b′ e q) r
```
