# 最高层含与站层号同形的层, 否定一路 (三): 接口 `LamIsoIf` 的盲区与边界

> 不含记号. 入口 [NegLamIso](NegLamIso.lagda.md). 对着接口 [LamIsoIf](LamIsoIf.lagda.md) ("接口定稿 2026-11-05 22:58 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 另导入 [NegLamIsoPre](NegLamIsoPre.lagda.md) (`Col`), [NegLeanLvBlind](NegLeanLvBlind.lagda.md) 的 `no-sim`, [LeanLvEmb](LeanLvEmb.lagda.md) 的 `stepE`, `supE`, `_∘E_` (都不改). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **`Prt` 挡住一种类的塌缩 (§2, 定理).** **`prt-br`**: `Prt` 在 $\Omega$-结点处, 对层号的**每个**坐标 $c$ 都有层的一支与 `g c` 忠实同形 (坐标映射 `cv Em` 有截面 `vc Em`, `cv-vc`). **`col-never-prt`**: 对一切种类 $\kappa_0$, 一切 $a$ : `HB SL`, 一切 $m$: `col κ₀ a` 不与 `st (2+m)` 忠实同形. **`ΛC-no-LamIso`**: 对一切 $\kappa_0$, `NegLamIsoPre` 的 $\Lambda_C$ 上没有 `LamIso` 的结构 (它的一切第一位置都不与 `st 2` 忠实同形). 这把接口头的判断 "常值坐标映射不满足 `Prt`" 写成了定理.
> 2. **边界 (§1, §3).** `prt→sim⁺`, `prt→sim` (忘掉嵌入). 所以 **`ΛF-no-LamIso`**: `ΛF` 上没有 `LamIso`; **`ΛF-no-own`**: 对一切 $n$, 没有 `OwnRd ΛF (3+n)` (由 `NegLeanLvBlind.no-sim`). 正面 **`prt2`**: $S_1$ 与 `st 2` 忠实同形 (嵌入 = `stepE ∘E supE 0`, 头 0); 所以 `Prt` 可满足, 头 2 在 `ΛF` 上有 `OwnRd` (`own2`).
> 3. **盲 (§4).** **`ownConst`** (对一切 $\Lambda$, 一切 `LamIso Λ`, 一切 $n$): `OwnRd Λ n` 有一个读回为常数 $1$ 的实例 (级层取 `L n`). 所以 "有 `OwnRd`" 不说明读回看数据, 也不说明它读出 `Lv (st n)` 的任何种类 (`ownConst-blind`). 实例 `own2` 同样不看数据. 读回是否沿 `π` 读, 只能对构造一路的实例写形状定理.
>
> **只否定什么.** `col-never-prt`, `ΛC-no-LamIso` 只否定: 把 `HB SL` 的高度塌缩成一个种类的常值结点 (`Col`) 当作忠实同形层. `ΛF-no-LamIso`, `ΛF-no-own` 只否定不改最高层. 都**不否定** `LamIso` 的路线 (接口要求 $\Lambda$ 改), 也不说构造一路的 $\Lambda'$ 怎样. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLamIsoBlind where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanLvIf using (Emb; j; cv; vc; cv-vc; Sim; sz; ss; sl; sΩ; Sim⁺; sz⁺; ss⁺; sl⁺; sΩ⁺)
open import OCF.Lean.LeanLvEmb using (stepE; supE; _∘E_)
open import OCF.Lean.LamIsoIf
open import OCF.Lean.NegLeanLvPre using (st-shape; Sg)
open import OCF.Lean.NegLeanLvBlind using (no-sim)
open import OCF.Lean.NegLamIsoPre using (L₀; module Col)
```

## §1 忘掉嵌入

```agda
module _ {T : KS} where
  prt→sim⁺ : ∀ {a x} → Prt T a x → Sim⁺ T a x
  prt→sim⁺ pz = sz⁺
  prt→sim⁺ (ps p) = ss⁺ (prt→sim⁺ p)
  prt→sim⁺ (pl pf sk) = sl⁺ (λ n → prt→sim⁺ (pf n)) sk
  prt→sim⁺ (pΩ Em ph sk) = sΩ⁺ (cv Em) (λ e → prt→sim⁺ (ph e)) sk

  prt→sim : ∀ {a x} → Prt T a x → Sim T a x
  prt→sim pz = sz
  prt→sim (ps p) = ss (prt→sim p)
  prt→sim (pl pf sk) = sl (λ n → prt→sim (pf n))
  prt→sim (pΩ Em ph sk) = sΩ (cv Em) (λ e → prt→sim (ph e))
```

## §2 每个坐标都有一支; 塌缩不忠实

`Br a b`: $b$ 是 $\Omega$-结点 $a$ 的一支.

```agda
  data Br : HB (step T) → HB (step T) → Set where
    br : ∀ {κ h} e → Br (hΩ κ h) (h e)

  prt-br : ∀ {a k g} → Prt T a (lΩ k g) → ∀ c → Σ (HB (step T)) (λ b → Br a b × Prt T b (g c))
  prt-br (pΩ {g = g} Em {h} ph sk) c =
    h (vc Em {inj₂ tt} c) , br _ , subst (λ z → Prt T (h (vc Em {inj₂ tt} c)) (g z)) (cv-vc Em {inj₂ tt} c) (ph (vc Em {inj₂ tt} c))

prt-ls-ls : ∀ {Z} → Prt SLs Z (ls lz) → ¬ Prt SLs Z (ls (ls lz))
prt-ls-ls (ps pz) (ps ())

H : ℕ → HB (Lv lz) → LH
H m = proj₁ (st-shape m)

to-shape : ∀ {a} m → Prt SLs a (stL (suc (suc m))) → Prt SLs a (lΩ lz (H m))
to-shape {a} m p = subst (Prt SLs a) (proj₁ (proj₂ (st-shape m))) p

module _ (κ₀ : K L₀) where
  open Col κ₀ using (col; ΛC)

  col-never-prt : ∀ a m → ¬ Prt SLs (col a) (stL (suc (suc m)))
  col-never-prt hz m p with prt-br (to-shape m p) hz
  ... | b , () , _
  col-never-prt (hs a) m p with prt-br (to-shape m p) hz
  ... | b , () , _
  col-never-prt (hl f) m p with prt-br (to-shape m p) hz
  ... | b , () , _
  col-never-prt (hΩ κ g) zero p with prt-br p hz | prt-br p (hs hz)
  ... | _ , br _ , q | _ , br _ , q′ = prt-ls-ls q q′
  col-never-prt (hΩ κ g) (suc m) p with prt-br (to-shape (suc m) p) hz
  ... | _ , br _ , q = col-never-prt (g (bot SL κ)) m (subst (Prt SLs _) (proj₂ (proj₂ (st-shape (suc m)))) q)

  col-down : ∀ {w x} a → x ⊲[ w ] col a → Σ (HB SL) (λ a′ → x ≡ col a′)
  col-down hz hself = hz , refl
  col-down (hs a) hself = hs a , refl
  col-down (hs a) (hsuc p) = col-down a p
  col-down (hl f) hself = hl f , refl
  col-down (hl f) (hlim n p) = col-down (f n) p
  col-down (hΩ κ g) hself = hΩ κ g , refl
  col-down (hΩ κ g) (hLim e p) = col-down (g (bot SL κ)) p

  hl-pos : ∀ {S : KS} {x : HB S} {F : ℕ → HB S} {w} → x ⊲[ w ] hl F → (x ≡ hl F) ⊎ Σ ℕ (λ n → x ⊲[ w ] F n)
  hl-pos hself = inj₁ refl
  hl-pos (hlim n p) = inj₂ (n , p)

  ΛC-no-LamIso : ¬ LamIso ΛC
  ΛC-no-LamIso I with hl-pos (L⊲ I 2 {w₀ L₀})
  ... | inj₁ e with prt-br (subst (λ t → Prt SLs t (stL 2)) e (prt I 2)) hz
  ...   | _ , () , _
  ΛC-no-LamIso I | inj₂ (n , p) with col-down (tw n) p
  ... | a′ , e = col-never-prt a′ 0 (subst (λ t → Prt SLs t (stL 2)) e (prt I 2))
```

## §3 边界: 不改最高层就没有; 头 2 有

```agda
ΛF-no-LamIso : ¬ LamIso ΛF
ΛF-no-LamIso I = no-sim 0 (L⊲ I 3 {w₀ L₀}) (prt→sim (prt I 3))

ΛF-no-own : ∀ n → ¬ OwnRd ΛF (suc (suc (suc n)))
ΛF-no-own n O = no-sim n (LvRd.ℓ⊲ (R O) {w₀ L₀}) (prt→sim (π O))

Em0 : Emb (FL lz) L₀
Em0 = stepE ∘E supE {ℕ} {FS} 0

prtC : (c : HB S⊥) → Prt SLs (up (hs hz ⊞ (hz ⊞ ιS 0 (up c)))) (ofHB (hs hz ⊞ ι {LH} {FL} lz (up c)))
prtC hz = ps pz
prtC (hs c) = ps (prtC c)
prtC (hl f) = pl (λ n → prtC (f n)) (λ _ → inj₂ tt)
prtC (hΩ (() , _) g)

prt2 : Prt SLs (Sg 1) (stL 2)
prt2 = pΩ Em0 (λ e → prtC e) (λ _ → inj₂ tt)
```

## §4 盲: 常数读回

```agda
ownConst : ∀ {Λ} → LamIso Λ → ∀ n → OwnRd Λ n
ownConst {Λ} I n = record
  { R = record { ℓ = L I n ; ℓ⊲ = L⊲ I n ; δ = λ _ _ → hs hz ; δLg = λ _ _ → tt ; δ-n1 = λ _ → refl }
  ; π = prt I n }

ownConst-blind : ∀ {Λ} (I : LamIso Λ) n {W} (lW : LgW L₀ W) (x y : Tree.D SLs (LvRd.ℓ (R (ownConst I n))) W) →
  LvRd.δ (R (ownConst I n)) lW x ≡ LvRd.δ (R (ownConst I n)) lW y
ownConst-blind I n lW x y = refl

own2 : OwnRd ΛF 2
own2 = record
  { R = record { ℓ = Sg 1 ; ℓ⊲ = hlim 1 hself ; δ = λ _ _ → hs hz ; δLg = λ _ _ → tt ; δ-n1 = λ _ → refl }
  ; π = prt2 }
```

**前提实例.** `prt-br` 的前提 `Prt T a (lΩ k g)`: `prt2`. `ownConst` 的前提 `LamIso Λ`: 构造一路的实例 (待查; 本篇不造). `col-never-prt` 与 `ΛC-no-LamIso` 的被否定对象 `col`, `ΛC` 是构造 (`NegLamIsoPre.Lg-ΛC`, `ΛC-sim`: 它们满足旧判据 `Sim⁺`).

## §5 结论 (按档)

- **[定理, 边界]** `prt→sim⁺`, `prt→sim`; **`ΛF-no-LamIso`**, **`ΛF-no-own`**; 正面 **`prt2`**, `own2`.
- **[定理, 否定]** **`prt-br`**; **`col-never-prt`**, `col-down`, **`ΛC-no-LamIso`**: 忠实同形排除一种类的塌缩 (对一切 $\kappa_0$).
- **[定理, 盲]** **`ownConst`**, `ownConst-blind`: `OwnRd` 有不看数据的实例 (只要有 `LamIso`).
- **[判断]** `Prt` 仍不要求不同结点用不同嵌入 (接口盲区 2); 一切同级结点共用一个嵌入时读回能否分开不同的分支, 要看构造一路的实例.
