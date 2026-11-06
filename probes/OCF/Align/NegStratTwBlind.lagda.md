# 分层互递归塔, 否定一路 (二): 接口的盲区与接口逼出的东西

> 不含记号. 入口 [NegStratTw](NegStratTw.lagda.md). 对着接口 [StratTwIf](StratTwIf.lagda.md) ("接口定稿 2026-11-05 19:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 1. **盲 (`trivSt`, `lvTriv`, `ownTriv`, 定理, 反模型).** `StratTw` 与 `OwnHd` 有一个平凡的共同实例: 总结构 `Tf = sup ℕ (λ s → step (Lev (fin s)))`, 前缀**不增长** (`P s = S₀`), 级是有限数 (`X s = fin s`, 没有 $\Omega$-结点), 对角 `Y s = fin s`, 头种类 `(s , inj₂ tt)`; 每个头种类的 `KLv` 的级层是自己的 `lyL (Y s)`, 读回**不看数据** (`rd … b x = b`, `blind-rd`), 升界是 ℕ 下标点更新. 所以接口不推出: 前缀增长, 级带 $\Omega$-结点, 级是对角的部分和, 读回进了闭项. 坍缩的类型 `CollLvFbTy` 有常数实例 (`NegKindLvBlind.collCFb`).
> 2. **接口逼出的 (定理, 非盲).**
>    - **`Y-inj`**: 对角两两不同 ($s<s'$ 时 $Y_s\ne Y_{s'}$), 由 `Yfst` 与高度的良基 (`no-up`: $\mathrm{hs}\,a\not\lhd a$). 所以 "所有站的级取同一个常数" 被接口排除 (要一个世界作前提; 实例 `GenK` 的 `w₀`).
>    - **`hd-inj`**: 在 `OwnHd` 下, 不同站的头种类不同. 所以 `OwnHd` 的实例回灌**无穷多个**种类 (对照 `NegKindLvInst.only-κ₁`: KindLv 只回灌一个). 这一点接口不盲.
>    - **`no-total`**: 任何 `StratTw T`, 任何站, `HB (Lev (X s))` 不是 `HB T` (由 `hdE` 与 `no-retract`). 级的高度类型永远不是总结构自己的高度类型.
>
> **只否定什么.** 反模型只否定推断 "有 `StratTw`/`OwnHd` 实例, 所以级是对角的部分和 / 读回读了数据 / 前缀增长". `Y-inj`, `hd-inj` 是正面定理 (接口排除的形状: 常数级, 有限个头种类). `no-total` 否定 "级就是总结构" 这一种取法. **不否定** 接口的任何记录, 不否定构造一路的实例 (见 [NegStratTwInst](NegStratTwInst.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegStratTwBlind where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (_≺ᴮ_; ≺s; ≺l; ≺Ω; Acc≺; acc; acc≺; irr≺)
open import OCF.Align.GenFoldIf using (GenK; tpK; TopG; top; DK)
open import OCF.Align.GenFoldInst using (genStep; genLev; genSupℕ; upd; upd-R; upd-Q; upd-at)
open import OCF.Align.KindLvIf using (KLv; ℓ; rd; lyL; LvFb)
open import OCF.Align.NegKindLvLev using (no-desc-at)
open import OCF.Align.NegStratTwCyc using (fin)
open import OCF.Align.StratTwIf
```

## §1 平凡实例

```agda
CFf : ℕ → KS
CFf s = step (Lev {S₀} (fin s))

Tf : KS
Tf = sup ℕ CFf

M₀ : KMap S₀ Tf
M₀ = record { j = λ κ → zero , inj₁ κ ; cv = λ κ e → e }

simFin : ∀ n → Sim M₀ (fin {Tf} n) (fin {S₀} n)
simFin zero = sz
simFin (suc n) = ss (simFin n)

lgFin : ∀ {S} n → LgB {S} (fin n)
lgFin zero = tt
lgFin (suc n) = lgFin n

trivSt : StratTw Tf
trivSt = record
  { P = λ _ → S₀ ; X = λ s → fin s ; M = λ _ → M₀ ; Y = λ s → fin s
  ; sim = simFin ; lY = lgFin ; Yfst = λ s → hself
  ; hd = λ s → s , inj₂ tt ; hdE = λ s → refl }

GTf : GenK Tf
GTf = genSupℕ CFf (λ s → genStep (genLev {S₀} (fin s)))

tpf : TopG Tf
tpf = tpK GTf

KTf : ∀ s → KLv Tf tpf (ΛS trivSt) (s , inj₂ tt)
KTf s = record
  { ℓ = lyL (fin {Tf} s) ; ℓ⊲ = λ {w} → hlim s hself
  ; rd = λ lW b x → b
  ; rd-fst = λ lW b x → hself
  ; rd-lg = λ lW b x lb → lb
  ; rs = λ w v → upd {λ m → Wd (CFf m)} w s (proj₁ (w s) , v)
  ; rs≤ = λ {w} {v} p → upd-R {λ m → Wd (CFf m)} (λ m → _≤w_ (CFf m)) w s (proj₁ (w s) , v)
                            (λ m → ≤w-rf (CFf m)) (≤w-rf (Lev {S₀} (fin s)) , p)
  ; rsLg = λ {w} {v} lw lv → upd-Q {λ m → Wd (CFf m)} (λ m → LgW (CFf m)) w s (proj₁ (w s) , v) lw (proj₁ (lw s) , lv)
  ; rs-top = λ {w} {v} → upd-at {λ m → Wd (CFf m)} w s (proj₁ (w s) , v) (λ u → proj₂ u ≡ v) refl }

lvTriv : LvFb Tf tpf (ΛS trivSt)
lvTriv (s , inj₂ tt) = inj₁ (KTf s)
lvTriv (s , inj₁ κ) = inj₂ tt

ownTriv : OwnHd trivSt tpf lvTriv
ownTriv s = KTf s , refl , refl
```

盲的三条 (`refl`):

```agda
blind-rd : ∀ s {W} (lW : LgW (step Tf) W) b (x : DK Tf (lyL (fin {Tf} s)) W) → rd (KTf s) lW b x ≡ b
blind-rd s lW b x = refl

blind-P : ∀ s → P trivSt s ≡ S₀
blind-P s = refl

blind-X : ∀ s → X trivSt s ≡ fin s
blind-X s = refl
```

## §2 高度的良基: $\mathrm{hs}\,a\not\lhd a$

`_⊑_`: 结构子项的自反传递闭包. 第一位置推出它 (`⊲→⊑`); 有 $a\prec y$ 与 $y\sqsubseteq a$ 就矛盾 (`noLoop`, 对 `Acc≺` 归纳).

```agda
module _ {S : KS} where
  data _⊑_ : HB S → HB S → Set where
    rf⊑ : ∀ {a} → a ⊑ a
    sn⊑ : ∀ {a b c} → a ⊑ b → b ≺ᴮ c → a ⊑ c

  cons⊑ : ∀ {a b c} → a ≺ᴮ b → b ⊑ c → a ⊑ c
  cons⊑ p rf⊑ = sn⊑ rf⊑ p
  cons⊑ p (sn⊑ q r) = sn⊑ (cons⊑ p q) r

  ⊲→⊑ : ∀ {a b w} → a ⊲[ w ] b → a ⊑ b
  ⊲→⊑ hself = rf⊑
  ⊲→⊑ (hsuc p) = sn⊑ (⊲→⊑ p) ≺s
  ⊲→⊑ (hlim n p) = sn⊑ (⊲→⊑ p) (≺l n)
  ⊲→⊑ (hLim e p) = sn⊑ (⊲→⊑ p) (≺Ω _)

  noLoop : ∀ {x} → Acc≺ x → ∀ {y} → x ≺ᴮ y → ¬ (y ⊑ x)
  noLoop ax p rf⊑ = irr≺ ax p
  noLoop (acc f) p (sn⊑ q r) = noLoop (f r) r (cons⊑ p q)

  no-up : ∀ {a w} → ¬ (hs a ⊲[ w ] a)
  no-up {a} p = noLoop (acc≺ a) ≺s (⊲→⊑ p)
```

## §3 接口逼出的: 对角两两不同, 头种类两两不同

```agda
module _ {T : KS} (St : StratTw T) where
  Y-chain : ∀ s k {w} → hs (Y St s) ⊲[ w ] Y St (suc k + s)
  Y-chain s zero = Yfst St s
  Y-chain s (suc k) = ⊲ᴮ-tr (hsuc (Y-chain s k)) (Yfst St (suc k + s))

  Y-inj : (w : Wd T) → ∀ s k → ¬ (Y St s ≡ Y St (suc k + s))
  Y-inj w s k e = no-up (subst (λ z → hs (Y St s) ⊲[ w ] z) (sym e) (Y-chain s k {w}))

  -- 级层的读数: KLv 给 ℓ, 有损给 0
  ℓof : ∀ {tp : TopG T} (κ : K T) → KLv T tp (ΛS St) κ ⊎ ⊤ → HB (step T)
  ℓof κ (inj₁ L) = ℓ L
  ℓof κ (inj₂ _) = hz

  hpred : ∀ {S} → HB S → HB S
  hpred (hs x) = x
  hpred x = x

  hd-inj : ∀ {tp : TopG T} {lv : LvFb T tp (ΛS St)} → OwnHd St tp lv → (w : Wd T) →
           ∀ s k → ¬ (hd St s ≡ hd St (suc k + s))
  hd-inj {tp} {lv} own w s k e = no-up {step T} {up (Y St s)} {w , hz} (subst (λ z → hs (up (Y St s)) ⊲[ w , hz ] z) (sym eqU) q)
    where
    s′ = suc k + s
    at : ∀ t → ℓof (hd St t) (lv (hd St t)) ≡ lyL (Y St t)
    at t with own t
    ... | L , p , q′ = trans (cong (ℓof (hd St t)) p) q′
    eqL : lyL (Y St s) ≡ lyL (Y St s′)
    eqL = trans (sym (at s)) (trans (cong (λ κ → ℓof κ (lv κ)) e) (at s′))
    eqU : up (Y St s) ≡ up (Y St s′)
    eqU = cong hpred eqL
    q : hs (up (Y St s)) ⊲[ w , hz ] up (Y St s′)
    q = up-⊲ (Y-chain s k {w})
```

前提可满足: `trivSt`, `ownTriv` 与世界 `w₀ GTf`.

```agda
open import OCF.Align.GenFoldIf using (w₀)

hd-inj-inst : ∀ s k → ¬ (hd trivSt s ≡ hd trivSt (suc k + s))
hd-inj-inst = hd-inj trivSt {tp = tpf} {lv = lvTriv} ownTriv (w₀ GTf)
```

## §4 级的高度类型不是总结构的

```agda
no-total : ∀ {T} (St : StratTw T) s → ¬ (HB (Lev (X St s)) ≡ HB T)
no-total {T} St s e = no-desc-at (hd St s) (trans (hdE St s) e) (λ x → x) (λ x → x) (λ x → refl)
```

前提 (一个 `StratTw`) 的实例: `trivSt`.

## §5 结论 (按档)

- **[定理, 反模型]** `trivSt`, `KTf`, `lvTriv`, **`ownTriv`**; `blind-rd`, `blind-P`, `blind-X`.
- **[定理]** `no-up`; **`Y-inj`**, **`hd-inj`** (前提实例 `hd-inj-inst`); **`no-total`**.
- **[判断]** `OwnHd` 比 `KindLvIf` 多绑了一件事 (级层是对角上第 $s$ 站的 `lyL (Y s)`), 由此逼出头种类无穷多 (`hd-inj`); 但不绑读回 (`blind-rd`) 与级的形状 (`blind-X`). 值要靠构造文件的实例形状定理.
