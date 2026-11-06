# NegSameV (五): 记录 `CrossV` 是盲的: 有一个实例, 非恒等搬运上只有无 $\Omega$-结点的插值

> 不含记号. 入口 [NegSameV](NegSameV.lagda.md). 对构造一路 SameV 的接口 [SameVIf](SameVIf.lagda.md) (定稿 2026-11-06 21:03, 本路不改它). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. 模块参数 `uipC` 是 `Cd` 上的 UIP (条件, 经 `ValCMono.monoΦ` 与自反方程).
>
> **`crossV` (条件定理, 条件 UIP).** `CrossV` 有一个实例: $\mathrm{Le}\,M\,x\,y$ 取 "存在**没有 $\Omega$-结点**的可数树 $p$ 使 $x\le p\le y$" (搬运任意), 或 "$M$ 是恒等搬运且 $x\le y$ (同层)". `cross-mono` 在前一种情形由 "折叠不看层号与界地作用在无 $\Omega$-结点的树上" (`fold-e`) 与同层单调 `monoΦ` 得到, 没有用到任何跨层的比较.
>
> **`blind`, `blind-top` (条件定理, 条件 UIP).** 这个实例里, 层号不同的搬运上, 左边是 $\Omega$-结点时 `Le` 不成立. 特别地, 在 `floor-block` 那一对层号上, 对搬运 `M₁₂`: `¬ Le M₁₂ (top (ω₁+1)) (top (ω₂+1))`.
>
> **读法.** 只用 `CrossV` 的字段 (`Le-id`, `Le-0`, `Le-z`, `cross-mono`) 推不出任何**含 $\Omega$-结点**的跨层比较. 所以 `P2` 不能只由 "`CrossV` 有实例" 得到; 证明的全部内容在具体的 `Le` 上的 "地板跨层相关" 一类引理. 接口要表达它, 须加字段 (例如 `Le M (top m) (top m′)`, 与 $\Omega$-结点的跨层规则).
>
>
> **后来的情况.** 构造一路的证明确实没有走 `CrossV`, 走的是具体的配对 `Match`, 关系 `LE`, 地板律 `tp`, `gtP` (判断: 与这里的读法一致). [NegSameVCheck](NegSameVCheck.lagda.md) 查它们.
>
> **前提实例.** `uipC`: 函数外延推出 (`ValCUip.fe→uipC`, 条件 Funext). `M₁₂`: [NegSameVMor](NegSameVMor.lagda.md) (定理). 实例的 `cross-mono` 的前提: 任一满足接口类型的数据; 实例不要求额外的东西.
>
> **只否定什么.** 只否定 "`CrossV` 的字段本身推出跨层比较". **不否定**: 构造一路的具体 `Le` 满足更多的律; 跨层比较成立; `P2`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase using (Cd)
open import Relation.Binary.PropositionalEquality using (_≡_)
module OCF.Lean.NegSameVBlind (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValCIf I₁ using (F)
open import OCF.Lean.ValCMono I₁ uipC using (monoΦ)
open import OCF.Lean.SameVIf
open import OCF.Lean.NegSameVMor using (M₁₂; m₁; m₂)
open import OCF.Lean.NegSameVSpine using (ω₁; ω₂; ω-ne)
```

## §1 无 $\Omega$-结点的树

`pur`: 可数树嵌入任一层. `φ`: 折叠在这种树上的作用 (不看层号, 目标, 界).

```agda
pur : ∀ {S : KS} → Cd → HB S
pur hz = hz
pur (hs x) = hs (pur x)
pur (hl f) = hl (λ n → pur (f n))
pur (hΩ () _)

φ : Cd → Cd
φ hz = hs hz
φ (hs p) = hl (mul (φ p))
φ (hl f) = hl (Σ⁺ (λ n → φ (f n)))
φ (hΩ () _)

Mo-pur : ∀ t p → MoAt t (pur p)
Mo-pur t hz = tt
Mo-pur t (hs p) = Mo-pur t p
Mo-pur t (hl f) = λ n → Mo-pur t (f n)
Mo-pur t (hΩ () _)

module E (t : Cd) where
  infix 4 _≈_
  _≈_ : H t → H t → Set
  a ≈ b = LeAt t a b × LeAt t b a

  e⊞ : ∀ (a b : Cd) → pur (a ⊞ b) ≈ pur a ⊞ pur b
  e⊞ a hz = L.≤-refl t _ , L.≤-refl t _
  e⊞ a (hs b) = Rel.s≤s (proj₁ (e⊞ a b)) , Rel.s≤s (proj₂ (e⊞ a b))
  e⊞ a (hl f) = Rel.l≤l (λ n → n) (L.idInc t) (λ n → proj₁ (e⊞ a (f n))) ,
                Rel.l≤l (λ n → n) (L.idInc t) (λ n → proj₂ (e⊞ a (f n)))
  e⊞ a (hΩ () _)

  ⊞≈ : ∀ {a b : H t} {p q : Cd} → a ≈ pur p → b ≈ pur q → a ⊞ b ≈ pur (p ⊞ q)
  ⊞≈ {p = p} {q = q} r s =
    L.≤-trans t (L.⊞-mono t (proj₁ r) (proj₁ s)) (proj₂ (e⊞ p q)) ,
    L.≤-trans t (proj₁ (e⊞ p q)) (L.⊞-mono t (proj₂ r) (proj₂ s))

  emul : ∀ {a : H t} {x : Cd} → a ≈ pur x → ∀ n → mul a n ≈ pur (mul x n)
  emul r zero = r
  emul r (suc n) = ⊞≈ (emul r n) r

  eΣ : ∀ (A : ℕ → H t) (f : ℕ → Cd) → (∀ n → A n ≈ pur (f n)) → ∀ n → Σ⁺ A n ≈ pur (Σ⁺ f n)
  eΣ A f r zero = r 0
  eΣ A f r (suc n) = ⊞≈ (eΣ A f r n) (r (suc n))

  hl≈ : ∀ {A : ℕ → H t} {f : ℕ → Cd} → (∀ n → A n ≈ pur (f n)) → hl A ≈ pur (hl f)
  hl≈ r = Rel.l≤l (λ n → n) (L.idInc t) (λ n → proj₁ (r n)) , Rel.l≤l (λ n → n) (L.idInc t) (λ n → proj₂ (r n))

fold-e : ∀ {m} (a : Acc b⊥ m) (lm : LgB m) t (pt : t ⊲ m) (b : H t) p → E._≈_ t (G a lm t pt b (pur p)) (pur (φ p))
fold-e a lm t pt b hz = L.≤-refl t _ , L.≤-refl t _
fold-e a lm t pt b (hs p) = E.hl≈ t (E.emul t (fold-e a lm t pt b p))
fold-e a lm t pt b (hl f) = E.hl≈ t (E.eΣ t _ _ (λ n → fold-e a lm t pt b (f n)))
fold-e a lm t pt b (hΩ () _)
```

## §2 实例

```agda
idMor : ∀ m → LvMor m m
idMor m = record
  { im = λ {t} _ → t ; im⊲ = λ q → q ; im-irr = λ _ _ → refl ; im-z = λ _ → refl
  ; im-⊲ = λ _ _ p → p ; im-s = λ _ _ p → p ; im-pp = λ _ _ p → p ; im-le = λ {t} _ → L.≤-refl hz t }

data IdC : ∀ {m m′} → LvMor m m′ → H m → H m′ → Set where
  idc : ∀ {m x y} → LeAt m x y → IdC (idMor m) x y

Pure : ∀ m m′ → H m → H m′ → Set
Pure m m′ x y = Σ Cd (λ p → LeAt m x (pur p) × LeAt m′ (pur p) y)

Lw : ∀ {m m′} → LvMor m m′ → H m → H m′ → Set
Lw {m} {m′} M x y = Pure m m′ x y ⊎ IdC M x y

-- 同层的恒等情形读出值关系 (层号的方程由 UIP 消去)
idLe : ∀ {m m′} {M : LvMor m m′} {x y} → IdC M x y → Σ (m ≡ m′) (λ e → LeAt m′ (subst H e x) y)
idLe (idc p) = refl , p

idLe′ : ∀ {m} {M : LvMor m m} {x y} → IdC M x y → LeAt m x y
idLe′ {m} {M} {x} {y} i with idLe i
... | e , p = subst (λ e′ → LeAt m (subst H e′ x) y) (uipC e refl) p

LwLe : ∀ {m} {M : LvMor m m} {x y} → Lw M x y → LeAt m x y
LwLe {m} (inj₁ (p , l , r)) = L.≤-trans m l r
LwLe (inj₂ i) = idLe′ i

cm : ∀ {m m′} (M : LvMor m m′) (lm : LgB m) (lm′ : LgB m′) {t} (q : t ⊲ m) {b b′ x y} →
     MoAt t b → MoAt (im M q) b′ → LeAt t (top b⊥ t) b → LeAt (im M q) (top b⊥ (im M q)) b′ →
     Lw (res M q) b b′ → MoAt m x → MoAt m′ y → Lw M x y →
     Lw (res M q) (F m lm t q b x) (F m′ lm′ (im M q) (im⊲ M q) b′ y)
cm {m} {m′} M lm lm′ {t} q {b} {b′} {x} {y} mb mb′ tb tb′ lb mx my (inj₁ (p , l , r)) = inj₁ (φ p , lL , lR)
  where
  aL = wf b⊥ m
  aR = wf b⊥ m′
  lL : LeAt t (F m lm t q b x) (pur (φ p))
  lL = L.≤-trans t (monoΦ (apWf m) aL aL lm lm q q (mb , mb , tb , L.≤-refl t b) (pur p) mx (Mo-pur m p) l)
                   (proj₁ (fold-e aL lm t q b p))
  lR : LeAt (im M q) (pur (φ p)) (F m′ lm′ (im M q) (im⊲ M q) b′ y)
  lR = L.≤-trans (im M q) (proj₂ (fold-e aR lm′ (im M q) (im⊲ M q) b′ p))
         (monoΦ (apWf m′) aR aR lm′ lm′ (im⊲ M q) (im⊲ M q) (mb′ , mb′ , tb′ , L.≤-refl (im M q) b′) y (Mo-pur m′ p) my r)
cm {m} .(idMor m) lm lm′ {t} q {b} {b′} {x} {y} mb mb′ tb tb′ lb mx my (inj₂ (idc p)) =
  inj₂ (idc (monoΦ (apWf m) (wf b⊥ m) (wf b⊥ m) lm lm′ q q (mb , mb′ , tb , LwLe {t} {idMor t} lb) y mx my p))

crossV : CrossV
crossV = record
  { Le = Lw
  ; idM = idMor
  ; Le-id = λ p → inj₂ (idc p)
  ; Le-0 = λ M → LwLe {hz} {M}
  ; Le-z = λ M y → inj₁ (hz , Rel.z≤ , Rel.z≤)
  ; cross-mono = cm }
```

## §3 盲

```agda
noΩ : ∀ m {κ g} p → ¬ LeAt m (hΩ κ g) (pur p)
noΩ m hz ()
noΩ m (hs p) (Rel.≤s r) = noΩ m p r
noΩ m (hl f) (Rel.≤l n r) = noΩ m (f n) r
noΩ m (hΩ () _) _

blind : ∀ {m m′} (M : LvMor m m′) {κ g y} → ¬ (m ≡ m′) → ¬ Lw M (hΩ κ g) y
blind {m} M ne (inj₁ (p , l , r)) = noΩ m p l
blind M ne (inj₂ i) = ne (proj₁ (idLe i))

m-ne : ¬ (m₁ ≡ m₂)
m-ne e = ω-ne (cong pd e)
  where
  pd : Cd → Cd
  pd (hs x) = x
  pd x = x

blind-top : ¬ Lw M₁₂ (top b⊥ m₁) (top b⊥ m₂)
blind-top = blind M₁₂ m-ne
```

## 结论 (按档)

- **[定理, 不用 UIP]** `pur`, `φ`, `Mo-pur`, `E.e⊞`, `E.⊞≈`, `E.emul`, `E.eΣ`, `E.hl≈`, **`fold-e`** (折叠在无 $\Omega$-结点的树上不看层号、目标与界, 与 `φ` 值相同); `idMor`; `noΩ`, `m-ne`.
- **[条件定理, 条件: `Cd` 上的 UIP]** **`crossV`**; **`blind`**, **`blind-top`**.
- **[判断]** `P2` 的证明内容不在 `CrossV` 的律里, 在具体 `Le` 的 "地板跨层相关".
