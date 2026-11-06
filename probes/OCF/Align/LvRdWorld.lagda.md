# 读回包 (三): 外层界 ω+1 之下以码为下标的世界 (瘦身版)

> 不含记号. 入口 [LvRd](LvRd.lagda.md), 接口 [LvRdIf](LvRdIf.lagda.md) §4. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 与 [LvFbCode](LvFbCode.lagda.md) 的 W2 世界相比, 三处瘦身 (都只为闭项所在的世界, 外层界固定为 $\omega+1$):
>
> 1. **码不带合法性证明.** `Cd` 是裸数据 (停, 进后继, 进第 $n$ 支); 不合法的码 (走不进界的路径) 的槽类型是 `S₀`, 闭项不用它们. 所以没有 `vB`, `vB-prop`, `tB`, `Σ`, 也没有 `A` 的码 (界 $\omega+1$ 不含 $\Omega$-结点).
> 2. **槽类型由码的结构给出** (`Pc`, 接口 §4): `kfin n` 处定义地是 `Sk n`, `kω` 处是 `Gω`. 不经 `eqG`/`toSk` 的搬运.
> 3. **世界只放槽** (`Wld = (k : Cd) → HB (Pc k)`), 不放分量的世界 (`LvFbCode.CW` 的 `Wd (P k)`): 折叠只读槽.
>
> 更新 `raise` 只在码的判等 `≟C` 上分情形. 四条律 (`at` 由 Hedberg 的码上 UIP, `off`, `mono`, `legal`) 是接口 `Raise` 的实例 `RaiseI`; 闭项与证书只用到 `raise`, `mono`, `legal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdWorld where

open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as N
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvRdIf using (Cd; cH; cP; cL; Pc; Wld; LgV; Raise)
```

## §1 码的相等可判定

```agda
tlC : Cd → Cd
tlC cH = cH
tlC (cP r) = r
tlC (cL n r) = r

≟C : (r s : Cd) → Dec (r ≡ s)
≟C cH cH = yes refl
≟C cH (cP s) = no (λ ())
≟C cH (cL m s) = no (λ ())
≟C (cP r) cH = no (λ ())
≟C (cP r) (cP s) with ≟C r s
... | yes refl = yes refl
... | no ne = no (λ e → ne (cong tlC e))
≟C (cP r) (cL m s) = no (λ ())
≟C (cL n r) cH = no (λ ())
≟C (cL n r) (cP s) = no (λ ())
≟C (cL n r) (cL m s) with n N.≟ m | ≟C r s
... | yes refl | yes refl = yes refl
... | no ne | _ = no (λ { refl → ne refl })
... | yes refl | no ne = no (λ e → ne (cong tlC e))
```

## §2 更新

```agda
private
  tp : ∀ {k₀ k} → k₀ ≡ k → HB (Pc k₀) → HB (Pc k)
  tp e δ = subst (λ j → HB (Pc j)) e δ

  lg-tp : ∀ {k₀ k} (e : k₀ ≡ k) δ → LgB δ → LgB (tp e δ)
  lg-tp refl δ l = l

upd : ∀ {k₀ k} → Dec (k₀ ≡ k) → HB (Pc k₀) → HB (Pc k) → HB (Pc k)
upd (yes e) δ x = x ⊞ tp e δ
upd (no _) δ x = x

raise : Wld → (k₀ : Cd) → HB (Pc k₀) → Wld
raise v k₀ δ k = upd (≟C k₀ k) δ (v k)

upd-≤ : ∀ {k₀ k} (d : Dec (k₀ ≡ k)) δ x {w} → x ⊲[ w ] upd d δ x
upd-≤ (yes e) δ x = ⊞-fst x (tp e δ)
upd-≤ (no _) δ x = hself

upd-lg : ∀ {k₀ k} (d : Dec (k₀ ≡ k)) δ x → LgB δ → LgB x → LgB (upd d δ x)
upd-lg (yes e) δ x lδ lx = Lg-⊞ x (tp e δ) lx (lg-tp e δ lδ)
upd-lg (no _) δ x lδ lx = lx

mono : ∀ v k₀ δ k {w} → v k ⊲[ w ] raise v k₀ δ k
mono v k₀ δ k = upd-≤ (≟C k₀ k) δ (v k)

legal : ∀ v k₀ δ → LgB δ → LgV v → LgV (raise v k₀ δ)
legal v k₀ δ lδ lv k = upd-lg (≟C k₀ k) δ (v k) lδ (lv k)

v₀ : Wld
v₀ k = hz

lv₀ : LgV v₀
lv₀ k = _
```

## §3 律 (`at` 由码上 UIP)

```agda
cd-uip : ∀ {r s : Cd} (e e′ : r ≡ s) → e ≡ e′
cd-uip = Decidable⇒UIP.≡-irrelevant ≟C

at : ∀ v k₀ δ → raise v k₀ δ k₀ ≡ v k₀ ⊞ δ
at v k₀ δ = go (≟C k₀ k₀)
  where
  go : (d : Dec (k₀ ≡ k₀)) → upd d δ (v k₀) ≡ v k₀ ⊞ δ
  go (yes e) = cong (λ e′ → v k₀ ⊞ tp e′ δ) (cd-uip e refl)
  go (no ne) = ⊥-elim (ne refl)

off : ∀ v k₀ δ k → ¬ (k₀ ≡ k) → raise v k₀ δ k ≡ v k
off v k₀ δ k ne = go (≟C k₀ k)
  where
  go : (d : Dec (k₀ ≡ k)) → upd d δ (v k) ≡ v k
  go (yes e) = ⊥-elim (ne e)
  go (no _) = refl

RaiseI : Raise
RaiseI = record { raise = raise ; at = at ; off = off ; mono = mono ; legal = legal }
```
