# 沿 View 递归 (七): 第 1 层的差树, 部分良基无条件

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 第 1 层 View `view₁` ([BrwViewKappa](BrwViewKappa.lagda.md)) 的合法性是 `HW` (View 的存在要它). 这里证: 在这个 View 上, **部分良基不要别的条件**. 度量是值 `toB` 在秩的比较下 ([BrwWfOneRank](BrwWfOneRank.lagda.md)):
>
> | View 的部分 | 整体的值的直接子树 | 部分的值 $\sqsubseteq$ 它, 因为 |
> |---|---|---|
> | 后继: $x$ | `bs (toB x)` 的 `toB x` | 字面 |
> | $\mathbb N$-极限: $x ⨾ (d_0⨾\dots⨾d_{n-1})$ | `bl (Sp …)` 的第 $n$ 项 | `ps-Sp` ($\equiv$) |
> | `ki`: $x$ 抬到 $W'$ 接 `J` | `bi` 在 $(W',p,l',y)$ 的分支 `I …(bw p (toB x))` | `Jle` (`J` 与 `I` 同形) + `Rv` (前缀抬升不升秩) |
> | `kκ`: $x$ 抬到 $c$ 接 `Cut` 接 $u(c)$ | `bκ` 在 $(c,p)$ 的分支 `S (K …) (u c)` | `CKs` (`Cut` 在 $c$ 里求值不超过 `K` 逐段求值, 逐段用 `Rv`) + `Smono` |
>
> 对比 [BrwViewOne](BrwViewOne.lagda.md) 的值一致: 那里两个方向都要, 反方向 (抬升不降值) 就是 `WSq`, 所以要 `HW`. 这里只要一个方向, 而 `Rv` 无条件. 所以 `wf₁` 是**无条件定理** (对 `HW` 树的这个 View; `HW` 只是 View 存在的条件).
>
> `rd₁≈`: 经 View 读出 `B₁` 的树, 与 `toB` 互相 $\preccurlyeq$ (一般的 `rd≈` 的实例).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfOne where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Pre; tailP; Cut)
open import OCF.Align.BrwMidZero using (dif)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; I; Ip; K; KR; toB)
open import OCF.Align.LayerTrRound using (⊲-idˡ)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwViewOne using (Sig₁; Ix₁; Cd₁; tg₁; K1; ki; kκ; X₁; val₁; Lgl₁; V₁; HW; J; ps; ps-Sp)
open import OCF.Align.BrwViewKappa using (vw; view₁)
open import OCF.Align.BrwWfDef
open import OCF.Align.BrwWfRead
open import OCF.Align.BrwWfOneRank
```

## §1 `J` 与 `I`: 同形, 底单调

```agda
module _ {W : A} (l : Lg W) (e : D azero W → D one W) where
  Jle  : ∀ {W₀} (z : D azero W₀) (q : W₀ ⊲ W) (w : D azero W) {c c′ : B₁ W} → c ⊑ c′ →
         S C.self l c (J e z q w) ⊑ I (λ w′ b → S C.self l b (e w′)) z q w c′
  Jlep : ∀ {W₀} (d : ℕ → D azero W₀) (q : W₀ ⊲ W) (w : D azero W) {c c′ : B₁ W} → c ⊑ c′ →
         ∀ n → Sp C.self l c (λ n → J e (d n) q (w ⨾ Pre q d n)) n ⊑ Ip (λ w′ b → S C.self l b (e w′)) d q w c′ n
  Jle n0 q w h = h
  Jle n1 q w h = Smono C.self l (e w) h
  Jle (x ⨾ y) q w h = Jle y q (w ⨾ nw q x) (Jle x q w h)
  Jle (nl d) q w h = bl-⊑ (Jlep d q w h)
  Jle (ni () u) q w h
  Jle (nκ () u) q w h
  Jle (nw p x) q w h = Jle x (⊲-tr p q) w h
  Jlep d q w h zero = h
  Jlep d q w h (suc n) = Jle (d n) q (w ⨾ Pre q d n) (Jlep d q w h n)
```

## §2 `Cut` 与 `K`

同 `BrwViewKappa.CK` 的形状 (对层 $b$ 归纳, 极限处 `tailP`), 只是 $\approx$ 换成一个方向的 $\sqsubseteq$, 逐段的 `WSq` 换成无条件的 `Rv`.

```agda
module _ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) where
  CKs  : ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) {Wt} (bW : b ⊲ Wt) (lT : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} →
         c₀ ⊑ x₀ → S C.self lT c₀ (Cut u b p aW lb bW) ⊑ K u b p aW lb x₀
  CKRs : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a)
         {Wt} (bW : alim f ⊲ Wt) (lT : Lg Wt) {x₀ : B₁ a} {c₀ : B₁ Wt} → c₀ ⊑ x₀ → ∀ m →
         Sp C.self lT (S C.self lT c₀ (Cut u (f n) p aW (wl n) (⊲-tr (C.lim n C.self) bW)))
            (λ m → Cut u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW)) m
         ⊑ KR u f st wl p aW x₀ m
  CKs b C.self aW lb bW lT h = h
  CKs (asuc c) (C.suc p) aW lb bW lT {x₀} {c₀} h =
    ⊑w (subst (λ t → S t lT (S C.self lT c₀ (Cut u c p aW lb r)) (u (⊲-tr aW p) lb) ⊑ S C.self lb (K u c p aW lb x₀) (u (⊲-tr aW p) lb))
              (⊲-idˡ r)
              (Rv (u (⊲-tr aW p) lb) C.self r lb lT (CKs c p aW lb r lT h)))
    where r = ⊲-tr (C.suc C.self) bW
  CKs (alim f) (C.lim n p) aW (st , wl) bW lT h = bl-⊑ (λ m → ⊑w (CKRs f st wl p aW bW lT h m))
  CKRs f st wl p aW bW lT h zero = CKs (f _) p aW (wl _) (⊲-tr (C.lim _ C.self) bW) lT h
  CKRs f st wl {n = n} p aW bW lT h (suc m) =
    CKs (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lT
        (CKRs f st wl p aW bW lT h m)
```

## §3 部分下降

`dec₁`: 与 `vw` 同形, 对 $y$ 归纳. 前缀的 View 的部分已经下降到 `toB x` 之下, 则整体的部分下降到 $S_q(\mathrm{toB}\,x, y)$ 之下. **`HW` 只当作 `vw` 的参数传过去, 证明里不用.**

```agda
Ob₁ : Set
Ob₁ = Obj Sig₁ X₁ val₁ Lgl₁

rk₁ : Ob₁ → T₁
rk₁ ((W , l) , x , _) = W , toB l x

Pt₁ : ∀ {i v} → V₁ i v → Ob₁ → Set
Pt₁ = Part Sig₁ X₁ val₁ Lgl₁

-- 前缀抬到 W′ 再求值, 秩不超过原来的值
base : ∀ {W W′} (l : Lg W) (l′ : Lg W′) (p : W ⊲ W′) (x : D one W) → S p l′ bz x ⊑ toB l x
base l l′ p x = subst (λ t → S t l′ bz x ⊑ toB l x) (⊲-idˡ p) (Rv x C.self p l l′ z⊑)

dec₁ : ∀ {W₀ W} (l : Lg W) (x : D one W) (hx : HW x) (vx : V₁ (W , l) (toB l x)) (q : W₀ ⊲ W) (y : D one W₀) (hy : HW y) →
       (∀ {o} → Pt₁ vx o → rk₁ o <ₛ (W , toB l x)) →
       ∀ {o} → Pt₁ (vw l x hx vx q y hy) o → rk₁ o <ₛ (W , S q l (toB l x) y)
dec₁ l x hx vx q n0 hy H p = H p
dec₁ l x hx vx q n1 hy H p-s = lt s-s (⊑-refl _)
dec₁ l x hx vx q (y₁ ⨾ y₂) (h₁ , h₂) H p =
  dec₁ l (x ⨾ nw q y₁) (hx , h₁) (vw l x hx vx q y₁ h₁) q y₂ h₂ (dec₁ l x hx vx q y₁ h₁ H) p
dec₁ l x hx vx q (nl d) hy H (p-l n) =
  lt (s-l n) (subst (λ t → t ⊑ Sp q l (toB l x) d n) (sym (ps-Sp q l (toB l x) d n)) (⊑-refl _))
dec₁ l x hx vx q (nw r y) hy H p = dec₁ l x hx vx (⊲-tr r q) y hy H p
dec₁ l x hx vx q (ni (ss C.self) u) hy H (p-Ω (W′ , p , l′ , y , ly) _) =
  lt (s-i p l′ y ly) (Jle l′ (λ w → u (⊲-tr q p) l′ w) (dif {W′} y (z⊲ y) ly) C.self n0 (⊑w (base l l′ p x)))
dec₁ l x hx vx q (nκ zz u) hy H (p-Ω (c , p , lc) _) =
  lt (s-κ p lc) (Smono C.self lc (u (⊲-tr q p) lc) (CKs u c p q lc C.self lc (base l lc p x)))
```

## §4 良基, 记录

```agda
_◁₁_ : Ob₁ → Ob₁ → Set
_◁₁_ = _◁_ Sig₁ X₁ val₁ Lgl₁ view₁

dec-top₁ : ∀ {o o′} → o′ ◁₁ o → rk₁ o′ <ₛ rk₁ o
dec-top₁ {(W , l) , x , hx} p = dec₁ l n0 tt (vz (z≼ , z≼)) C.self x hx (λ ()) p

wf₁ : WellFounded _◁₁_
wf₁ = measure _◁₁_ _<ₛ_ rk₁ <ₛ-wf dec-top₁

view₁ᵂ : BrwViewᵂ Sig₁ X₁ val₁ Lgl₁
view₁ᵂ = record { bv = view₁ ; wf = wf₁ }
```

## §5 经 View 读出 `B₁`: 值一致

```agda
allC₁ : ∀ {i} {k : Sig.Kd Sig₁ i} (c : Sig.Cd Sig₁ {i} k) → Sig.LgC Sig₁ {i} {k} c
allC₁ c = tt

bΩ-m₁ : ∀ {i} (k : K1) {f g : (c : Cd₁ {i} k) → B₁ (proj₁ (tg₁ {i} {k} c))} → (∀ c → f c ≼ g c) →
        Sig.bΩ Sig₁ {i} k f ≼ Sig.bΩ Sig₁ {i} k g
bΩ-m₁ ki h = i≼ (λ p l y ly → ≼i p l y ly (h (_ , p , l , y , ly)))
bΩ-m₁ kκ h = κ≼ (λ p lc → ≼κ p lc (h (_ , p , lc)))

Cong₁ : Cong view₁ᵂ
Cong₁ = record { tr = ≼-trans ; bs-m = s≼s ; bl-m = λ h → l≼ (λ n → ≼l n (h n)) ; bΩ-m = λ {i} k h → bΩ-m₁ {i} k h }

rd₁ : (o : Ob₁) → B₁ (proj₁ (proj₁ o))
rd₁ o = Read.rd view₁ᵂ (λ {i} {k} c → allC₁ {i} {k} c) o

rd₁≈ : ∀ o → (rd₁ o ≼ val₁ {proj₁ o} (proj₁ (proj₂ o))) × (val₁ {proj₁ o} (proj₁ (proj₂ o)) ≼ rd₁ o)
rd₁≈ o = ReadOk.rd≈ view₁ᵂ (λ {i} {k} c → allC₁ {i} {k} c) Cong₁ o
```
