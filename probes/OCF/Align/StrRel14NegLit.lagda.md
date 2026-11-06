# 结构关系, 第十四轮的否定 (四): `CP` 分支对不是 `CPᴸ`; 合法的 Ω-极限层在 `CP` 分支对上可以值递减

> 不读记号. 入口 [StrRel14Neg](StrRel14Neg.lagda.md). 对着 [StrRel14If](StrRel14If.lagda.md) (接口定稿 2026-11-05) 写. 接口的 `κˣ` 只在 `CPᴸ` (= `CP` 加字面 $c\lhd c'$) 分支对上比分支, 理由写在接口的 "已知的缺口". 本文给这个选择两条编译证据, 并指出它留给可靠性证明的负担.
>
> 1. **`cpω`, `¬⊲₁₂`, `¬⊲₂₁`, `¬cpᴸ`**: $\omega$ 的两种写法 $\omega_1=\lim_n n$, $\omega_2=\lim_n (n+1)$, 从树世界 $0$ 出发的两条路径 (`lim 0 self`, `lim 0 (suc self)`) 是一个 `CP` 对 (对齐 `aL`, 顶端可比, 自洽, 全部写出), 但两个方向都没有字面的 $\lhd$, 所以不是 `CPᴸ`.
> 2. **`Λh`, `lΛh`, `hdec`, `¬litH`, `¬relBr`**: 一个合法的 Ω-极限层 $\Lambda_h=\mathrm{h\Omega}\,g$, $g\,c=\mathrm{emb}(h\,c)$, $h$ 对字面的 $\lhd$ 单调 (`hA⊲`, 所以 `LgH` 成立), 但 $h\,\omega_1=\omega\cdot2$, $h\,\omega_2=\omega$ (`hdec`: $h\,\omega_2+1\le h\,\omega_1$). 于是在 `CP` 对 $(\omega_1,\omega_2)$ 上, $\Omega_{\Lambda_h}$ 的两个分支节点的坐标层**左边在值上严格大**, 字面上没有 $g\,\omega_1\sqsubseteq_\infty g\,\omega_2$ (`¬litH`), 所以两个分支不 `RelX` 相关 (`¬relBr`).
> 3. **`no-ht`**: 没有把高度严格单调 (沿 `_⊏_`) 地映到可数值 `A` 的函数. 所以 "值上的 `rk-mono`" 若想经一个值函数 $H\to A$ 来写, 在含 $\Omega$-极限的层上写不出; 要写成 $H$ 上的关系.
>
> **构造一路为什么需要这些.** `κˣ` 的可靠性 (`RelX` ⇒ `SemX` 的 `nκ` 一句) 要在折叠沿格路径走到的每个位置对上用分支的关系. 走到的位置对由对齐 `Al` 给出 (`StrRel12Sem.WalkR` 的 `posCP`), 只带值上的 $c\le c'$; 第 1 条说这样的对可以不是 `CPᴸ`, 第 2 条说在合法的层上这样的对里分支的坐标层可以值递减. 所以 (判断, 依据这两条与 `StrRel12Sem.WalkR` 的前提 `h`, `sb`): `κˣ` 的可靠性不能照 `StrRel12Kp.sem-κ` 那样把分支的关系喂给走法; 走法里出现的分支对要么限制成字面的 (要换对齐), 要么分支的关系从别处来.
>
> **只否定什么.** 第 1 条否定 "`CP` ⇒ 字面 $c\lhd c'$" (两个方向), 第 2 条否定 "合法的 Ω-极限层的分支在 `CP` 对上坐标层值单调" 与 "`CP` 对上的 `Ωd` 分支 `RelX` 相关". 不否定 `κˣ` 本身, 不否定 `κˣ` 的可靠性 (没有编译 $\Lambda_h$ 上折叠的值), 不涉及 $\Omega^{\mathsf H}$ ($g=\mathrm{emb}$ 对值单调, 判断).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14NegLit where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; irr; _⊞_)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hl; hΩ; hself; sL; ni; n1; D; ⊲ᴴ0)
open import OCF.Align.HtFeedHt using (emb; emb⊲; Lg-emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aL)
open import OCF.Align.StrRel12Al using (CP; Coh)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
```

## 1 $\omega$ 的两种写法, 一个 `CP` 对

```agda
nA : ℕ → A
nA zero = azero
nA (suc n) = asuc (nA n)

lgN : ∀ n → Lg (nA n)
lgN zero = tt
lgN (suc n) = lgN n

cohN : ∀ n → Coh (lgN n)
cohN zero = tt
cohN (suc n) = cohN n

-- ω 的两种写法
f₁ f₂ : ℕ → A
f₁ n = nA n
f₂ n = nA (suc n)

ω₁ ω₂ : A
ω₁ = alim f₁
ω₂ = alim f₂

l₁ : Lg ω₁
l₁ = (λ n → C.suc C.self) , (λ n → lgN n)
l₂ : Lg ω₂
l₂ = (λ n → C.suc C.self) , (λ n → lgN (suc n))

c₁ : Coh {a = ω₁} l₁
c₁ = (λ n → refl) , (λ n → cohN n)
c₂ : Coh {a = ω₂} l₂
c₂ = (λ n → refl) , (λ n → cohN (suc n))

-- 值
⊞N : ∀ k n → nA k ⊞ nA n ≡ nA (n + k)
⊞N k zero = refl
⊞N k (suc n) = cong asuc (⊞N k n)

≡≤ : ∀ {a b} → a ≡ b → a ≤ b
≡≤ {a} refl = ≤-refl a

nle : ∀ k → nA k ≤ ω₁
nle k = ≤l k (≤-refl _)

nle′ : ∀ n k → nA n ≤ nA (n + k)
nle′ zero k = z≤
nle′ (suc n) k = s≤ (nle′ n k)

adm : ∀ k → Adm (nA k) (nA (suc k)) ω₁ ω₂
adm k = ω₁ , l≤ (λ n → ≤l n (≤-trans (nle′ n k) (≡≤ (sym (⊞N k n))))) ,
             l≤ (λ n → ≤l (n + k) (≡≤ (trans (⊞N (suc k) n) (cong nA (+-suc n k)))))

-- 分支世界对 (ω₁, ω₂): 两边从 0 起, 对齐, 顶端可比, 自洽
al : Al ω₁ ω₂ (C.lim {f = f₁} 0 C.self) l₁ (C.lim {f = f₂} 0 (C.suc C.self)) l₂
al = aL (aS (C.suc C.self) tt) (λ m → aP (aS {a = nA (m + 0)} {a′ = nA (suc (m + 0))} C.self (lgN (suc (suc (m + 0))))) (s≤′ (m + 0)) (adm (m + 0)))
  where
  s≤′ : ∀ k → nA k ≤ nA (suc k)
  s≤′ k = ≤-suc (≤-refl (nA k))

ω≤ : ω₁ ≤ ω₂
ω≤ = l≤ (λ n → ≤l n (≤-suc (≤-refl (nA n))))

cpω : CP {V = azero} {V′ = azero} tt tt (C.lim {f = f₁} 0 C.self) l₁ (C.lim {f = f₂} 0 (C.suc C.self)) l₂
cpω = (al , adm0 , refl , refl) , ω≤ , c₁ , c₂
  where
  adm0 : Adm azero azero ω₁ ω₂
  adm0 = ω₁ , proj₁ (proj₂ (adm 0)) , l≤ (λ n → ≤l n (≤-trans (≡≤ (⊞N 0 n)) (≤-suc (≡≤ (cong nA (+-identityʳ n))))))
```

## 2 这个 `CP` 对不是 `CPᴸ`

```agda
split⊲ : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (C.Strict a b)
split⊲ C.self = inj₁ refl
split⊲ (C.suc p) = inj₂ (C.ss p)
split⊲ (C.lim n p) = inj₂ (C.sl n p)

hdA : A → A
hdA (alim f) = f 0
hdA _ = azero

¬lim⊲fin : ∀ {f} k → ¬ (alim f ⊲ nA k)
¬lim⊲fin zero ()
¬lim⊲fin (suc k) (C.suc p) = ¬lim⊲fin k p

¬⊲₁₂ : ¬ (ω₁ ⊲ ω₂)
¬⊲₁₂ h with split⊲ h
... | inj₁ e = z≢1 (cong hdA e)
  where z≢1 : ¬ (azero ≡ asuc azero)
        z≢1 ()
... | inj₂ (C.sl n p) = ¬lim⊲fin (suc n) p

¬⊲₂₁ : ¬ (ω₂ ⊲ ω₁)
¬⊲₂₁ h with split⊲ h
... | inj₁ e = o≢0 (cong hdA e)
  where o≢0 : ¬ (asuc azero ≡ azero)
        o≢0 ()
... | inj₂ (C.sl n p) = ¬lim⊲fin n p

¬cpᴸ : ¬ If.CPᴸ hz tt {V = azero} {V′ = azero} tt tt (C.lim {f = f₁} 0 C.self) l₁ (C.lim {f = f₂} 0 (C.suc C.self)) l₂
¬cpᴸ (_ , h) = ¬⊲₁₂ h
```

## 3 合法的 Ω-极限层, 在这个 `CP` 对上值递减

```agda
-- 一个合法的 Ω-极限层, 分支对字面的 ⊲ 单调, 对值不单调
sel : A → A → A
sel azero x = x ⊞ ω₁
sel (asuc _) x = x
sel (alim _) x = x

hA : A → A
hA azero = azero
hA (asuc a) = asuc (hA a)
hA (alim f) = sel (f 0) (alim (λ n → hA (f n)))

⊲sel : ∀ a x → x ⊲ sel a x
⊲sel azero x = C.lim 0 C.self
⊲sel (asuc _) x = C.self
⊲sel (alim _) x = C.self

hA⊲ : ∀ {c c′} → c ⊲ c′ → hA c ⊲ hA c′
hA⊲ C.self = C.self
hA⊲ (C.suc p) = C.suc (hA⊲ p)
hA⊲ {c′ = alim f} (C.lim n p) = C.⊲-tr (C.lim n (hA⊲ p)) (⊲sel (f 0) (alim (λ n → hA (f n))))

lg⊞ω : ∀ x → Lg x → Lg (x ⊞ ω₁)
lg⊞ω x l = (λ n → C.suc C.self) , go
  where
  go : ∀ n → Lg (x ⊞ nA n)
  go zero = l
  go (suc n) = go n

lgSel : ∀ a x → Lg x → Lg (sel a x)
lgSel azero x l = lg⊞ω x l
lgSel (asuc _) x l = l
lgSel (alim _) x l = l

lgh : ∀ c → Lg c → Lg (hA c)
lgh azero l = tt
lgh (asuc c) l = lgh c l
lgh (alim f) (st , l) = lgSel (f 0) _ ((λ n → hA⊲ (st n)) , (λ n → lgh (f n) (l n)))

gH : A → H
gH c = emb (hA c)

Λh : H
Λh = hΩ gH

lΛh : LgH Λh
lΛh = (λ _ p → ⊲ᴴ0 (emb⊲ (hA⊲ p))) , (λ c l → Lg-emb (hA c) (lgh c l))

-- 值: hA ω₂ + 1 ≤ hA ω₁ (分支对 (ω₁, ω₂) 上, 左边的坐标层值上严格大)
hAn : ∀ k → nA k ≤ hA (nA k)
hAn zero = z≤
hAn (suc k) = s≤ (hAn k)

hdec : asuc (hA ω₂) ≤ hA ω₁
hdec = ≤l 1 (s≤ (l≤ (λ n → ≤l (suc n) (≤-refl _))))

-- 与接口对接: 在实例 Λh 里, CP 对 (ω₁, ω₂) 上 Ωd Λh 的两个分支不 RelX 相关
open Rk Λh lΛh using (_⊑∞_; s∞; u∞; l∞; L∞)
open If Λh lΛh using (RelX; niˣ)

-- 不含 Ω-极限的高度的值
hv : H → A
hv hz = azero
hv (hs b) = asuc (hv b)
hv (hl f) = alim (λ n → hv (f n))
hv (hΩ g) = azero

hv-emb≤ : ∀ x → hv (emb x) ≤ x
hv-emb≤ azero = z≤
hv-emb≤ (asuc x) = s≤ (hv-emb≤ x)
hv-emb≤ (alim f) = l≤ (λ n → ≤l n (hv-emb≤ (f n)))

hv-emb≥ : ∀ x → x ≤ hv (emb x)
hv-emb≥ azero = z≤
hv-emb≥ (asuc x) = s≤ (hv-emb≥ x)
hv-emb≥ (alim f) = l≤ (λ n → ≤l n (hv-emb≥ (f n)))

hv⊑ : ∀ {a} x → a ⊑∞ emb x → hv a ≤ hv (emb x)
hv⊑ azero s∞ = ≤-refl _
hv⊑ (asuc x) s∞ = ≤-refl _
hv⊑ (alim f) s∞ = ≤-refl _
hv⊑ (asuc x) (u∞ p) = ≤-suc (hv⊑ x p)
hv⊑ (alim f) (l∞ n p) = ≤l n (hv⊑ (f n) p)

¬litH : ¬ (gH ω₁ ⊑∞ gH ω₂)
¬litH h = irr (hA ω₂) (≤-trans hdec (≤-trans (hv-emb≥ (hA ω₁)) (≤-trans (hv⊑ (hA ω₂) h) (hv-emb≤ (hA ω₂)))))

brL : D Λh ω₁
brR : D Λh ω₂
brL = ni (sL {c = ω₁} C.self hself) (λ _ _ _ → n1)
brR = ni (sL {c = ω₂} C.self hself) (λ _ _ _ → n1)

¬relBr : ¬ RelX Λh Λh l₁ l₂ brL brR
¬relBr (niˣ k _) = ¬litH k
```

## 4 没有严格单调的值函数

```agda
module NoHt where
  open Rk Ωᴴ Lg-Ωᴴ using (_⊏_; cs; cl; cL) renaming (s∞ to s∞ᴼ)

  StrictV : (H → A) → Set
  StrictV ht = ∀ {a b} → a ⊏ b → asuc (ht a) ≤ ht b

  s→≤ : ∀ {a b} → asuc a ≤ b → a ≤ b
  s→≤ h = ≤-trans (≤-suc (≤-refl _)) h

  ge : ∀ ht → StrictV ht → ∀ c → c ≤ ht (emb c)
  ge ht m azero = z≤
  ge ht m (asuc c) = ≤-trans (s≤ (ge ht m c)) (m (cs s∞ᴼ))
  ge ht m (alim f) = l≤ (λ n → ≤-trans (ge ht m (f n)) (s→≤ (m (cl n s∞ᴼ))))

  no-ht : ∀ ht → ¬ StrictV ht
  no-ht ht m = irr (ht Ωᴴ) (≤-trans (s≤ (ge ht m (ht Ωᴴ))) (m (cL (ht Ωᴴ) s∞ᴼ)))
```
