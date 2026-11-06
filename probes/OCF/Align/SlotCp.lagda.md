# 高度坐标的共享槽 (二): 级的和里的拷贝是共享槽

> 不含记号. 入口 [Slot](Slot.lagda.md), 接口 [SlotIf](SlotIf.lagda.md), 一般构造 [SlotGen](SlotGen.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> [NegStratTwDeep](NegStratTwDeep.lagda.md) §1 的 `Cp.kup`: `Lev (a ⊞ b)` 里有 `Lev a` 的种类的拷贝, 坐标类型对 $b$ 递归**化到** `Lev a` 的坐标类型 (不重建树, 来回由 `refl` 在递归的底给出). 那里只取沿 "第 0 支 / 最小坐标支" 的一条路径. 本篇:
>
> - **§1 三种提升 (对一切共享槽).** 恒等 `idSlot` (一个成员, 就是共享种类自己); `step` 的旧种类 `stepSlot`; 并的**一切**分量 `supSlot` (成员下标是 $\Sigma\,I\,J_i$, $I$ 任意, 可以含函数; 写世界时一切分量一起写, 不判定); 并的**一个** $\mathbb N$-分量 `supℕSlot` (按 `upd` 换掉第 $n$ 个分量, $\mathbb N$ 可判定).
> - **§2 沿一切路径的拷贝.** `Path b`: $b$ 的一切路径 (ℕ-极限取任一 $n$, $\Omega$-极限取任一坐标). `kupP b p κ`: 沿路径 $p$ 的拷贝. **`cpSlot a κ b : Slot (Lev (a ⊞ b)) _ (Path b) (kupP b · κ) (Lev a) _ κ`**: 共享槽是 `Lev a` (它的世界) 与种类 $\kappa$, 对 $b$ 的构造子递归, 由 §1 的三种提升拼出. `al0`: 基世界里每份共享世界都是 `Lev a` 的基世界 (证据的实例).
> - **§3 坐标是高度的种类.** `rsNew a′ : RsK (Lev (hs a′)) _ (inj₂ tt)`: `step` 的新种类 (坐标 `HB (Lev a′)`) 上精确置自己 (`step` 的第二分量, 位置可判定). 于是 **`famNew a′ b`**: `Lev (hs a′ ⊞ b)` 里新种类沿一切路径的拷贝 (坐标都是 `HB (Lev a′)` 的高度, 下标是含函数的路径) 在带证据的世界上**一起**满足 `RsK`, 不判定下标.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SlotCp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; tpK; w₀)
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.GenFoldInst using (genLev; topSupG; upd; upd-R; upd-Q; upd-at)
open import OCF.Align.RsOwnIf using (RsK; subW; topSub)
open import OCF.Align.SlotIf
open import OCF.Align.SlotGen using (module Gen)
```

## §1 三种提升

```agda
module _ {Q : KS} {tq : TopG Q} {κ₀ : K Q} where
  idSlot : Slot Q tq ⊤ (λ _ → κ₀) Q tq κ₀
  idSlot = record
    { cE = λ _ e → e ; cE⁻ = λ _ x → x ; cE⁻-cE = λ _ e → refl
    ; wpr = λ _ w → w ; lgπ = λ _ l → l ; pr→ = λ _ p → p ; pr← = λ _ p → p
    ; lgE→ = λ _ l → l ; lgE← = λ _ l → l ; top-cp = λ _ w → refl
    ; Al = λ P w → P w ; al-map = λ f p → f p ; al-pr = λ _ p → p
    ; wset = λ ω w → ω ; al-set = λ ω w → refl ; set-≤ = λ p → p ; set-least = λ q p → p
    ; set-lg = λ lw lω → lω }

  stepSlot : ∀ {T tp J κJ} → Slot T tp J κJ Q tq κ₀ → Slot (step T) (topStepG tp) J (λ j → inj₁ (κJ j)) Q tq κ₀
  stepSlot {T} S = record
    { cE = cE S ; cE⁻ = cE⁻ S ; cE⁻-cE = cE⁻-cE S
    ; wpr = λ j w → wpr S j (proj₁ w) ; lgπ = λ j lw → lgπ S j (proj₁ lw)
    ; pr→ = λ j p → pr→ S j p ; pr← = λ j p → pr← S j p
    ; lgE→ = lgE→ S ; lgE← = lgE← S
    ; top-cp = λ j w → top-cp S j (proj₁ w)
    ; Al = λ P w → Al S P (proj₁ w) ; al-map = λ f p → al-map S f p ; al-pr = λ j p → al-pr S j p
    ; wset = λ ω w → wset S ω (proj₁ w) , proj₂ w
    ; al-set = λ ω w → al-set S ω (proj₁ w)
    ; set-≤ = λ al → set-≤ S al , hself
    ; set-least = λ q al → set-least S (proj₁ q) al , proj₂ q
    ; set-lg = λ lw lω → set-lg S (proj₁ lw) lω , proj₂ lw }

  -- 并的一切分量: 成员下标 Σ I J, I 任意; 一切分量一起写
  supSlot : (I : Set) (F : I → KS) (tps : (i : I) → TopG (F i)) (Js : I → Set) (κs : ∀ i → Js i → K (F i)) →
            (∀ i → Slot (F i) (tps i) (Js i) (κs i) Q tq κ₀) →
            Slot (sup I F) (topSupG I F tps) (Σ I Js) (λ ij → proj₁ ij , κs (proj₁ ij) (proj₂ ij)) Q tq κ₀
  supSlot I F tps Js κs Ss = record
    { cE = λ ij → cE (Ss (proj₁ ij)) (proj₂ ij)
    ; cE⁻ = λ ij → cE⁻ (Ss (proj₁ ij)) (proj₂ ij)
    ; cE⁻-cE = λ ij → cE⁻-cE (Ss (proj₁ ij)) (proj₂ ij)
    ; wpr = λ ij w → wpr (Ss (proj₁ ij)) (proj₂ ij) (w (proj₁ ij))
    ; lgπ = λ ij lw → lgπ (Ss (proj₁ ij)) (proj₂ ij) (lw (proj₁ ij))
    ; pr→ = λ ij p → pr→ (Ss (proj₁ ij)) (proj₂ ij) p
    ; pr← = λ ij p → pr← (Ss (proj₁ ij)) (proj₂ ij) p
    ; lgE→ = λ ij l → lgE→ (Ss (proj₁ ij)) (proj₂ ij) l
    ; lgE← = λ ij l → lgE← (Ss (proj₁ ij)) (proj₂ ij) l
    ; top-cp = λ ij w → top-cp (Ss (proj₁ ij)) (proj₂ ij) (w (proj₁ ij))
    ; Al = λ P w → ∀ i → Al (Ss i) P (w i)
    ; al-map = λ f p i → al-map (Ss i) f (p i)
    ; al-pr = λ ij p → al-pr (Ss (proj₁ ij)) (proj₂ ij) (p (proj₁ ij))
    ; wset = λ ω w i → wset (Ss i) ω (w i)
    ; al-set = λ ω w i → al-set (Ss i) ω (w i)
    ; set-≤ = λ al i → set-≤ (Ss i) (al i)
    ; set-least = λ q al i → set-least (Ss i) (q i) (al i)
    ; set-lg = λ lw lω i → set-lg (Ss i) (lw i) lω }
```

$\mathbb N$-分量里的一个: 用 `upd` (对 $n$ 与 $m$ 的构造子同时递归). `upd-L` 是 `upd-R` 的另一边.

```agda
upd-L : ∀ {P : ℕ → Set} (R : ∀ m → P m → P m → Set) (w w′ : (m : ℕ) → P m) n (x : P n) →
        (∀ m → R m (w m) (w′ m)) → R n x (w′ n) → ∀ m → R m (upd {P} w n x m) (w′ m)
upd-L R w w′ zero x q r zero = r
upd-L R w w′ zero x q r (suc m) = q (suc m)
upd-L R w w′ (suc n) x q r zero = q zero
upd-L {P} R w w′ (suc n) x q r (suc m) =
  upd-L {λ k → P (suc k)} (λ k → R (suc k)) (λ k → w (suc k)) (λ k → w′ (suc k)) n x (λ k → q (suc k)) r m

module _ {Q : KS} {tq : TopG Q} {κ₀ : K Q} where
  supℕSlot : (F : ℕ → KS) (tps : (i : ℕ) → TopG (F i)) (n : ℕ) {J : Set} {κJ : J → K (F n)} →
             Slot (F n) (tps n) J κJ Q tq κ₀ → Slot (sup ℕ F) (topSupG ℕ F tps) J (λ j → n , κJ j) Q tq κ₀
  supℕSlot F tps n S = record
    { cE = cE S ; cE⁻ = cE⁻ S ; cE⁻-cE = cE⁻-cE S
    ; wpr = λ j w → wpr S j (w n) ; lgπ = λ j lw → lgπ S j (lw n)
    ; pr→ = λ j p → pr→ S j p ; pr← = λ j p → pr← S j p
    ; lgE→ = lgE→ S ; lgE← = lgE← S
    ; top-cp = λ j w → top-cp S j (w n)
    ; Al = λ P w → Al S P (w n) ; al-map = λ f p → al-map S f p ; al-pr = λ j p → al-pr S j p
    ; wset = λ ω w → upd {λ m → Wd (F m)} w n (wset S ω (w n))
    ; al-set = λ ω w → upd-at {λ m → Wd (F m)} w n (wset S ω (w n)) (Al S (λ x → x ≡ ω)) (al-set S ω (w n))
    ; set-≤ = λ {ω} {w} al → upd-R {λ m → Wd (F m)} (λ m → _≤w_ (F m)) w n (wset S ω (w n)) (λ m → ≤w-rf (F m)) (set-≤ S al)
    ; set-least = λ {ω} {w} {w′} q al → upd-L {λ m → Wd (F m)} (λ m → _≤w_ (F m)) w w′ n (wset S ω (w n)) q (set-least S (q n) al)
    ; set-lg = λ {ω} {w} lw lω → upd-Q {λ m → Wd (F m)} (λ m → LgW (F m)) w n (wset S ω (w n)) lw (set-lg S (lw n) lω) }
```

## §2 沿一切路径的拷贝

```agda
Path : ∀ {S : KS} → HB S → Set
Path hz = ⊤
Path (hs b) = Path b
Path (hl f) = Σ ℕ (λ n → Path (f n))
Path {S} (hΩ κ g) = Σ (E S κ) (λ c → Path (g c))

module Cp {S : KS} (a : HB S) (κ : K (Lev a)) where
  kupP : ∀ b → Path b → K (Lev (a ⊞ b))
  kupP hz p = κ
  kupP (hs b) p = inj₁ (kupP b p)
  kupP (hl f) p = proj₁ p , kupP (f (proj₁ p)) (proj₂ p)
  kupP (hΩ κ′ g) p = proj₁ p , kupP (g (proj₁ p)) (proj₂ p)

  cpSlot : ∀ b → Slot (Lev (a ⊞ b)) (tpK (genLev (a ⊞ b))) (Path b) (kupP b) (Lev a) (tpK (genLev a)) κ
  cpSlot hz = idSlot
  cpSlot (hs b) = stepSlot (cpSlot b)
  cpSlot (hl f) = supSlot ℕ (λ n → Lev (a ⊞ f n)) (λ n → tpK (genLev (a ⊞ f n))) (λ n → Path (f n))
                          (λ n → kupP (f n)) (λ n → cpSlot (f n))
  cpSlot (hΩ κ′ g) = supSlot (E S κ′) (λ c → Lev (a ⊞ g c)) (λ c → tpK (genLev (a ⊞ g c))) (λ c → Path (g c))
                             (λ c → kupP (g c)) (λ c → cpSlot (g c))

  -- 基世界: 每份共享世界都是 Lev a 的基世界
  al0 : ∀ b → Al (cpSlot b) (λ x → x ≡ w₀ (genLev a)) (w₀ (genLev (a ⊞ b)))
  al0 hz = refl
  al0 (hs b) = al0 b
  al0 (hl f) = λ n → al0 (f n)
  al0 (hΩ κ′ g) = λ c → al0 (g c)

  ev0 : ∀ b → ShW (cpSlot b) (w₀ (genLev (a ⊞ b)))
  ev0 b = w₀ (genLev a) , al0 b

  -- 沿 "第 0 支 / 最小坐标支" 的一条路径 (NegStratTwDeep.Cp.kup 走的那条)
  botP : ∀ (b : HB S) → Path b
  botP hz = tt
  botP (hs b) = botP b
  botP (hl f) = 0 , botP (f 0)
  botP (hΩ κ′ g) = bot S κ′ , botP (g (bot S κ′))
```

## §3 `step` 的新种类 (坐标是高度) 的拷贝

```agda
rsNew : ∀ {S : KS} (a′ : HB S) → RsK (Lev (hs a′)) (tpK (genLev (hs a′))) (inj₂ tt)
rsNew a′ = record
  { rs = λ w v → proj₁ w , v
  ; rs≤ = λ p → ≤w-rf (Lev a′) , p
  ; rsLg = λ lw lv → proj₁ lw , lv
  ; rs-top = refl }

module CpNew {S : KS} (a′ : HB S) (b : HB S) where
  open Cp (hs a′) (inj₂ tt) public

  SN : Slot (Lev (hs a′ ⊞ b)) (tpK (genLev (hs a′ ⊞ b))) (Path b) (kupP b) (Lev (hs a′)) (tpK (genLev (hs a′))) (inj₂ tt)
  SN = cpSlot b

  open Gen SN (rsNew a′) public

  -- 一切路径上的拷贝 (坐标 HB (Lev a′)) 一起有 RsK
  famNew : RsFam (subW (Lev (hs a′ ⊞ b)) (ShW SN)) (topSub (tpK (genLev (hs a′ ⊞ b)))) (Path b) (kupP b)
  famNew = famS

  -- 坐标类型逐字是 HB (Lev a′) (经 cE, 对 b 递归)
  coordNew : ∀ p → E (Lev (hs a′ ⊞ b)) (kupP b p) → HB (Lev a′)
  coordNew p = cE SN p
```

## §4 结论 (按档)

- **[构造]** `idSlot`, `stepSlot`, `supSlot` (并的一切分量, 下标任意), `supℕSlot`; `Cp.cpSlot` (对一切 `S`, `a`, `κ`, `b`); `rsNew`; **`CpNew.famNew`**: `Lev (hs a′ ⊞ b)` 里 `step` 新种类 (坐标是高度 `HB (Lev a′)`) 沿一切路径的拷贝, 在带证据 `ShW` 的世界上一起满足 `RsK`, 不判定下标.
- **[定理]** `Cp.al0`, `Cp.ev0` (证据在基世界上有实例, 所以 `ShW` 不是空真; 成员族非空, 例如 `botP b`); `upd-L`.
- **[判断]** 这里的成员坐标类型都**化到同一个** (`HB (Lev a′)`), 所以共享槽是成员自己所在的那个级 `Lev (hs a′)`, 不撞 `no-retract`: 成员与槽的坐标类型一样, 不需要把更大的类型收缩进来. 坐标类型真正随下标变的一族 (`K₁` 的 `κHc c`) 不在这一类里, 见 [SlotKH](SlotKH.lagda.md).
