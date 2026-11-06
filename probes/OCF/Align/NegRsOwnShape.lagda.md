# 升界只剩一种? 否定一路 (二): 接口 `RsOwnIf` 的每种形状

> 不含记号. 入口 [NegRsOwn](NegRsOwn.lagda.md). 对着接口 [RsOwnIf](RsOwnIf.lagda.md) ("接口定稿 2026-11-05 19:21 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 对接口的每个记录给盲定理 (律满足了, 想要的性质却没有) 与边界定理 (再加一条就矛盾或推出分离子). 实例都落在 `K₁ = Kc 1 = sup (⊤ ⊎ H₀) (FN S₀)` 上 (定义相等, 所以 `PW (⊤ ⊎ H₀) (FN S₀)` 的记录直接说 `K₁`); 种类族是读回分量 `inj₂ (jx f)` 的底拷贝 `κ₁ f` (坐标 `A`) 与分量 `inj₂ (hs (jx f))` 的新种类 `κH f` (坐标 `HB (Lev (jx f))`).
>
> | 形状 | 本篇的定理 | 档 |
> |---|---|---|
> | `RsK` | `rsK∘` (可判定种类上的实例), `rsK-moves` (实例把别的种类的界也升了: `RsK` 不管别处), `decJ→RsK` (下标含函数的 `κ₁ f`, 条件 `DecJ`) | 定理 / 条件 |
> | `RsK` + `Keep` (族) | **`keepFam-sep`** (`κ₁`), **`keepFamH-sep`** (`κH`): ⇒ 分离子; `keep∘` (可判定处成立), `decJ→keepFam` (条件 `DecJ` 下整个前提成立) | 否定 / 实例 |
> | `AllFam` | **`all→own`**, **`own→all`**: 与 `OwnFam` 逻辑等价 (`inV` 可以带 $j$), 所以 "不依赖 $j$" 不约束什么 (盲) | 定理 (盲) |
> | `AllFam`, `inV` 不依赖 $j$ | **`no-allΨ`**, **`no-allFam`**: 对两个**可判定地不同**的下标就矛盾, $\Psi$ 可依赖分量 | 否定 |
> | `OwnFam` | `decJ→OwnFam` (条件 `DecJ`); 无条件的否定: 未走通 (见 `NegRsOwnPre` §4) | 条件 |
> | `RsBd` | **`rsBd-empty`** (`U` 空), **`rsBd-triv`** (`U` 逼 $v$ 等于旧顶: 恒等世界就满足): 不定 `U` 时盲; **`no-bd-top`**: `rsᵇ-top` 去掉前提就矛盾 | 盲; 否定 |
> | `subW`, `RsInv` | **`rsInv-empty`** ($P$ 空); **`sh-same`**, **`sh-all-top`**: $P$ 让下标不同的底拷贝的界相等时, 世界里这些种类分不开, 精确置自己就是一起置; **`inv→surj`**, **`no-sh-ι0`**: 坐标是高度的种类共用一个 "同一个 $a$" 的界时, 编码必须满射, 经第 0 个分量的编码不满射 | 盲; 否定 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRsOwnShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.LvKtIf using (FN)
open import OCF.Align.GenFoldIf using (K₁; TopG; top)
open import OCF.Align.NegGenFoldUpd using (jx; jx-inj; Sep; WDec; wdec→sep; κ₁; z₁; fω; upd∘)
open import OCF.Align.NegKindLvRaise using (tp₁; two; one; no21; wA)
open import OCF.Align.NegKindLvUpd using (κH)
open import OCF.Align.NegRsOwnPre using (inj₂-inj; DecJ; module WithDecJ)
open import OCF.Align.RsOwnIf
```

## §1 `RsK`: 可判定种类上的实例; 它不管别处

```agda
open PW (⊤ ⊎ H₀) (FN S₀)

-- 旧站分量 inj₁ tt 的底种类 (下标可判定)
rsK∘ : RsK K₁ tp₁ (inj₁ tt , tt)
rsK∘ = record
  { rs = upd∘
  ; rs≤ = λ { p (inj₁ tt) → p ; p (inj₂ c) → ≤w-rf (Lev c) }
  ; rsLg = λ { lw lv (inj₁ tt) → lv ; lw lv (inj₂ c) → lw (inj₂ c) }
  ; rs-top = refl }

keep∘ : Keep tp₁ (inj₁ tt) tt rsK∘
keep∘ = record { keep = λ { w v (inj₁ tt) ne → ⊥-elim (ne refl) ; w v (inj₂ c) ne → refl } }

-- 同一个种类, 另一个 RsK: 把一切 κH 拷贝的界也升一格
upH : Wd K₁ → A → Wd K₁
upH w v (inj₁ tt) = v
upH w v (inj₂ hz) = w (inj₂ hz)
upH w v (inj₂ (hs c)) = proj₁ (w (inj₂ (hs c))) , hs (proj₂ (w (inj₂ (hs c))))
upH w v (inj₂ (hl g)) = w (inj₂ (hl g))
upH w v (inj₂ (hΩ κ g)) = w (inj₂ (hΩ κ g))

rsK-moves : RsK K₁ tp₁ (inj₁ tt , tt)
rsK-moves = record
  { rs = upH
  ; rs≤ = λ { p (inj₁ tt) → p ; p (inj₂ hz) → C.self
            ; {w} p (inj₂ (hs c)) → ≤w-rf (Lev c) , hsuc hself
            ; {w} p (inj₂ (hl g)) → ≤w-rf (Lev (hl g)) ; {w} p (inj₂ (hΩ κ g)) → ≤w-rf (Lev (hΩ κ g)) }
  ; rsLg = λ { lw lv (inj₁ tt) → lv ; lw lv (inj₂ hz) → lw (inj₂ hz) ; lw lv (inj₂ (hs c)) → lw (inj₂ (hs c))
             ; lw lv (inj₂ (hl g)) → lw (inj₂ (hl g)) ; lw lv (inj₂ (hΩ κ g)) → lw (inj₂ (hΩ κ g)) }
  ; rs-top = refl }

-- 它确实升了下标含函数的别的种类
moves-κH : ∀ f w v → Bd K₁ (κH f) (hs (proj₂ (w (inj₂ (hs (jx f)))))) (rs rsK-moves w v)
moves-κH f w v = hself

moves-strict : ∀ f w v → proj₂ (rs rsK-moves w v (inj₂ (hs (jx f)))) ≡ hs (proj₂ (w (inj₂ (hs (jx f)))))
moves-strict f w v = refl

-- 下标含函数的 κ₁ f: 条件实例
decJ→RsK : DecJ → ∀ f → RsK K₁ tp₁ (κ₁ f)
decJ→RsK D f = record
  { rs = λ w v → rsJ w f v ; rs≤ = λ {w} {v} p → rs≤J w f v p
  ; rsLg = λ lw lv → rsLgJ f lw lv ; rs-top = λ {w} {v} → rs-topJ w f v }
  where open WithDecJ D
```

## §2 `Keep` (族): 推出分离子

只用 `rs-top` 与 `keep`, 不用 `rs≤`, `rsLg`. 世界取基世界 `z₁`, 把 `κ₁ f` 置成 $1$, 看 `κ₁ f′` 的界是不是 $0$.

```agda
keepFam-sep : (R : ∀ f → RsK K₁ tp₁ (κ₁ f)) → (∀ f → Keep tp₁ (inj₂ (jx f)) (0 , tt) (R f)) → Sep
keepFam-sep R Kp = wdec→sep wd
  where
  wd : WDec
  wd f f′ = go (rs (R f) z₁ one (inj₂ (jx f′)) 0) refl
    where
    W : Wd K₁
    W = rs (R f) z₁ one
    own : jx f′ ≡ jx f → W (inj₂ (jx f′)) 0 ≡ one
    own e = subst (λ g → W (inj₂ (jx g)) 0 ≡ one) (sym (jx-inj e)) (rs-top (R f) {z₁} {one})
    kept : ¬ (jx f′ ≡ jx f) → W (inj₂ (jx f′)) 0 ≡ azero
    kept ne = cong (λ x → x 0) (Keep.keep (Kp f) z₁ one (inj₂ (jx f′)) (λ e → ne (inj₂-inj e)))
    go : ∀ r → W (inj₂ (jx f′)) 0 ≡ r → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
    go azero e = inj₁ (λ q → z≢1 (trans (sym e) (own q)))
      where z≢1 : azero ≡ one → ⊥
            z≢1 ()
    go (asuc r) e = inj₂ (λ ne → s≢z (trans (sym e) (kept ne)))
      where s≢z : asuc r ≡ azero → ⊥
            s≢z ()
    go (alim g) e = inj₂ (λ ne → l≢z (trans (sym e) (kept ne)))
      where l≢z : alim g ≡ azero → ⊥
            l≢z ()

-- 坐标是高度的种类 κH f
keepFamH-sep : (R : ∀ f → RsK K₁ tp₁ (κH f)) → (∀ f → Keep tp₁ (inj₂ (hs (jx f))) (inj₂ tt) (R f)) → Sep
keepFamH-sep R Kp = wdec→sep wd
  where
  wd : WDec
  wd f f′ = go (proj₂ (rs (R f) z₁ (hs hz) (inj₂ (hs (jx f′))))) refl
    where
    W : Wd K₁
    W = rs (R f) z₁ (hs hz)
    own : jx f′ ≡ jx f → proj₂ (W (inj₂ (hs (jx f′)))) ≡ hs hz
    own e = subst (λ g → proj₂ (W (inj₂ (hs (jx g)))) ≡ hs hz) (sym (jx-inj e)) (rs-top (R f) {z₁} {hs hz})
    kept : ¬ (jx f′ ≡ jx f) → proj₂ (W (inj₂ (hs (jx f′)))) ≡ hz
    kept ne = cong proj₂ (Keep.keep (Kp f) z₁ (hs hz) (inj₂ (hs (jx f′))) (λ e → ne (hs-inj (inj₂-inj e))))
      where hs-inj : ∀ {x y : H₀} → hs x ≡ hs y → x ≡ y
            hs-inj refl = refl
    go : ∀ r → proj₂ (W (inj₂ (hs (jx f′)))) ≡ r → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
    go hz e = inj₁ (λ q → z≢1 (trans (sym e) (own q)))
      where z≢1 : _≡_ {A = HB (Lev (jx f′))} hz (hs hz) → ⊥
            z≢1 ()
    go (hs r) e = inj₂ (λ ne → n≢ (trans (sym e) (kept ne)))
      where n≢ : hs r ≡ hz → ⊥
            n≢ ()
    go (hl g) e = inj₂ (λ ne → n≢ (trans (sym e) (kept ne)))
      where n≢ : hl g ≡ hz → ⊥
            n≢ ()
    go (hΩ κ g) e = inj₂ (λ ne → n≢ (trans (sym e) (kept ne)))
      where n≢ : hΩ κ g ≡ hz → ⊥
            n≢ ()

-- 前提可满足: 可判定处 (keep∘); 下标含函数处在 DecJ 下 (经典地成立, 判断)
decJ→keepFam : (D : DecJ) → ∀ f → Keep tp₁ (inj₂ (jx f)) (0 , tt) (decJ→RsK D f)
decJ→keepFam D f = record { keep = kp }
  where
  open DecJ D
  open WithDecJ D
  kp : ∀ w v i → ¬ (i ≡ inj₂ (jx f)) → rsJ w f v i ≡ w i
  kp w v (inj₁ tt) ne = refl
  kp w v (inj₂ c) ne = go (isJ c f) (isJ-ok c f)
    where
    go : ∀ b → (b ≡ true → c ≡ jx f) → pick b c (w (inj₂ c)) v ≡ w (inj₂ c)
    go true ok = ⊥-elim (ne (cong inj₂ (ok refl)))
    go false ok = refl
```

**两半各自可满足** (`keepFam-sep`, `keepFamH-sep`): 只要 `Keep` 不要 `RsK`: 世界不动; 只要 `RsK` 不要 `Keep`: `decJ→RsK` (条件 `DecJ`); 两者同时: 可判定种类上 `rsK∘`, `keep∘`; 下标含函数处在 `DecJ` 下 `decJ→keepFam`. 后者不是空真的依据: `DecJ` 经典地成立 (判断), 而 `keepFam-sep` 说它推出分离子, 两者相容.

## §3 `AllFam` 与 `OwnFam` 等价; "同一个 $\Psi$" 的两种读法

**盲.** `AllFam` 的 $\Psi$ 不依赖 $j$, 但回灌值经 `inV j` 进 $V$, 而 $V$ 可以是 $\Sigma\,J\,(\ldots)$: `inV j v = (j , v)` 把 $j$ 带进去. 所以 `AllFam` 与 `OwnFam` 逻辑等价 (对一切积世界).

```agda
module FamEq {I : Set} {F : I → KS} {tp : TopG (sup I F)} {J : Set} {ix : J → I} {κJ : (j : J) → K (F (ix j))} where
  private module Q = PW I F

  all→own : Q.AllFam tp J ix κJ → Q.OwnFam tp J ix κJ
  all→own P = record
    { R = Q.AllFam.R P
    ; vi = λ j → record { Φ = λ i x v → Q.AllFam.Ψ P i x (Q.AllFam.inV P j v) ; rs≡ = Q.AllFam.rs≡ P j } }

  own→all : Q.OwnFam tp J ix κJ → Q.AllFam tp J ix κJ
  own→all P = record
    { V = Σ J (λ j → E (F (ix j)) (κJ j))
    ; inV = λ j v → j , v
    ; Ψ = λ { i x (j , v) → Q.ViaΦ.Φ (Q.OwnFam.vi P j) i x v }
    ; R = Q.OwnFam.R P
    ; rs≡ = λ j w v i → Q.ViaΦ.rs≡ (Q.OwnFam.vi P j) w v i }
```

**边界.** 若两份**可判定地不同**的底拷贝 (`κ₁ fω` 与 `κ₁ f₁`, 第 1 项分别是 $0$ 与 $1$) 的 `RsK` 用同一个 rs, 就矛盾 (`no-same-rs`). 世界 `wS` 按下标的第 1 项 (模式匹配, 不判定相等) 给 `κ₁ fω` 界 $0$, 给 `κ₁ f₁` 界 $2$; 对 `κ₁ fω` 升到 $1$ (前提 $0\lhd 1$), `rs≤` 要 `κ₁ f₁` 的界 $\unrhd 2$, 而同一个 rs 对 `κ₁ f₁` 的 `rs-top` 说它是 $1$. 推论 `no-allFam`: `AllFam` 若 `inV` 在这两个下标上一样 (比如 $V=A$, `inV j v = v`), 矛盾; $\Psi$ 可以任意依赖分量. 这是 `NegKindLvRaise.no-klv-upAllR` (只对 "每份拷贝同一个 $R$") 的加强: 不要求对每个分量同一个算子, 只要求两个种类共用一个 rs.

```agda
f₁ : ℕ → H₀
f₁ _ = hs hz

gS : (x y : H₀) → Wd (Lev x)
gS hz hz = azero
gS hz (hs _) = two
gS hz (hl _) = azero
gS hz (hΩ _ _) = azero
gS (hs x) y = dWLev (hs x)
gS (hl g) y = dWLev (hl g)
gS (hΩ κ g) y = dWLev (hΩ κ g)

wS : Wd K₁
wS (inj₁ tt) = azero
wS (inj₂ hz) = azero
wS (inj₂ (hs c)) = dWLev (hs c)
wS (inj₂ (hl h)) = λ { zero → gS (h zero) (h (suc zero)) ; (suc n) → dWLev (h (suc n)) }
wS (inj₂ (hΩ κ g)) = dWLev (hΩ κ g)

wS-0 : wS (inj₂ (jx fω)) 0 ≡ azero
wS-0 = refl

wS-1 : wS (inj₂ (jx f₁)) 0 ≡ two
wS-1 = refl

no-same-rs : (R₀ : RsK K₁ tp₁ (κ₁ fω)) (R₁ : RsK K₁ tp₁ (κ₁ f₁)) →
  (∀ w v i → rs R₀ w v i ≡ rs R₁ w v i) → ⊥
no-same-rs R₀ R₁ eq = no21 (subst (two ⊲_) e p)
  where
  p : two ⊲ rs R₀ wS one (inj₂ (jx f₁)) 0
  p = rs≤ R₀ {wS} {one} (C.suc C.self) (inj₂ (jx f₁)) 0
  e : rs R₀ wS one (inj₂ (jx f₁)) 0 ≡ one
  e = trans (cong (λ x → x 0) (eq wS one (inj₂ (jx f₁)))) (rs-top R₁ {wS} {one})

no-allFam : (P : AllFam tp₁ (ℕ → H₀) (λ f → inj₂ (jx f)) (λ f → (0 , tt))) →
  (∀ v → AllFam.inV P fω v ≡ AllFam.inV P f₁ v) → ⊥
no-allFam P ic = no-same-rs (R fω) (R f₁)
  (λ w v i → trans (rs≡ fω w v i) (trans (cong (Ψ i (w i)) (ic v)) (sym (rs≡ f₁ w v i))))
  where open AllFam P
```

**两半各自可满足** (`no-same-rs`): 只要 `rs-top` 与同一个 rs: 每份底拷贝都置成 $v$ (`NegKindLvRaise.upAllR (λ a v → v)`, `half-top`); 只要 `rs≤` 与同一个 rs: 恒等; 两个 `RsK` 各自 (不共用 rs): `decJ→RsK` (条件 `DecJ`). 对固定的 `fω`, `f₁`, 可判定的分量上 (`inj₁ tt`) 的 `rsK∘` 说 `RsK` 本身可满足.

## §4 `RsBd`: 不定 `U` 时盲; `rsᵇ-top` 的前提是被逼的

```agda
rsBd-empty : ∀ {T tp κ Up} → RsBd T tp κ Up (λ _ _ _ → ⊥)
rsBd-empty = record
  { rsᵇ = λ w u v q → w ; rsᵇ≤ = λ q → ⊥-elim q ; rsᵇLg = λ q _ _ → ⊥-elim q
  ; rsᵇ-top = λ q _ → ⊥-elim q ; rsᵇ-up = λ q → ⊥-elim q }

-- U 逼 v 等于旧顶时, 世界不动就满足一切律
rsBd-triv : ∀ {T tp κ Up} → RsBd T tp κ Up (λ w u v → top tp κ w ≡ v)
rsBd-triv {T} = record
  { rsᵇ = λ w u v q → w ; rsᵇ≤ = λ q → ≤w-rf T ; rsᵇLg = λ q lw lv → lw
  ; rsᵇ-top = λ q _ → q ; rsᵇ-up = λ {w} {u} q → u }

-- 前提被逼: 无前提的 rs-top + 无前提的不降 矛盾 (把自己置成低于旧界的 v)
no-bd-top : ∀ f (B : RsBd K₁ tp₁ (κ₁ f) (λ _ → ⊤) (λ _ _ _ → ⊤)) →
  (∀ {w u v} (q : ⊤) → top tp₁ (κ₁ f) (rsᵇ B w u v q) ≡ v) → ⊥
no-bd-top f B rt = one⊀0 (subst (one ⊲_) (rt {wA one} {tt} {azero} tt) (rsᵇ≤ B {wA one} {tt} {azero} tt (inj₂ (jx f)) 0))
  where
  one⊀0 : ¬ (one ⊲ azero)
  one⊀0 ()
```

## §5 `subW`, `RsInv`

**盲.** $P$ 空时一切 `RsInv` 律空真 (接口已说; 这里是定理).

```agda
rsInv-empty : ∀ {T tp κ} → RsInv T (λ _ → ⊥) tp κ
rsInv-empty = record
  { rsᴵ = λ w p v → w ; rsᴵ-P = λ p v → p ; rsᴵ≤ = λ p _ → ⊥-elim p
  ; rsᴵLg = λ p _ _ → ⊥-elim p ; rsᴵ-top = λ p → ⊥-elim p }
```

**共享界的世界里, 底拷贝分不开.** `ShJ P`: $P$ 的世界里一切 `κ₁ f` 的界相等 (构造一路的 "一切底拷贝的界都等于同一个 $a$" 推出它, 见 `NegRsOwnInst`). 那么: `κ₁ f` 与 `κ₁ f′` 在 `subW K₁ P` 的每个世界里有同样的界 (`sh-same`); 任何 `RsInv` 精确置 `κ₁ f` 的同时也精确置了一切 `κ₁ f′` (`sh-all-top`); `no-same-rs` 的世界 `wS` 不在 $P$ 里 (`wS-not-sh`). 所以共享界的升界是 "一起置", 它躲开 `no-same-rs` 与 `no-klv-upAllR` 的办法是**把拷贝不同的世界排除掉**, 不是一种新的 "只置自己" 的形状.

```agda
ShJ : (Wd K₁ → Set) → Set
ShJ P = ∀ {w} → P w → ∀ f f′ → w (inj₂ (jx f)) 0 ≡ w (inj₂ (jx f′)) 0

sh-same : ∀ {P} → ShJ P → ∀ f f′ {c} (w : Wd (subW K₁ P)) → Bd (subW K₁ P) (κ₁ f) c w → Bd (subW K₁ P) (κ₁ f′) c w
sh-same sh f f′ {c} w b = subst (c ⊲_) (sh (proj₂ w) f f′) b

sh-all-top : ∀ {P} → ShJ P → ∀ f (R : RsInv K₁ P tp₁ (κ₁ f)) {w} (p : P w) v f′ → top tp₁ (κ₁ f′) (rsᴵ R w p v) ≡ v
sh-all-top sh f R p v f′ = trans (sym (sh (rsᴵ-P R p v) f f′)) (rsᴵ-top R p)

wS-not-sh : ∀ {P} → ShJ P → ¬ P wS
wS-not-sh sh p = z≢2 (sh p fω f₁)
  where z≢2 : azero ≡ two → ⊥
        z≢2 ()

-- 前提可满足: 共享界的一个 P 与它的一个世界
Psh : Wd K₁ → Set
Psh w = Σ A (λ a → ∀ f → w (inj₂ (jx f)) 0 ≡ a)

sh-Psh : ShJ Psh
sh-Psh (a , h) f f′ = trans (h f) (sym (h f′))

z₁-Psh : Psh z₁
z₁-Psh = azero , λ f → refl
```

**坐标是高度的种类: 共享界要满射的编码.** 对 `κH f`, 坐标类型 `HB (Lev (jx f))` 随 $f$ 变, "同一个 $a$" 要经编码 `emb f : X → HB (Lev (jx f))`. `PE emb w`: 一切 `κH f′` 的界都是 `emb f′ a` (同一个 $a$). 若 `RsInv` 在 `PE emb` 上精确置 `κH f`, 则 `emb f` 满射 (`inv→surj`). 经第 0 个分量的编码 (`embι f = ι 0`, 把 $H_0$ 放进 `Lev (jx f)` 的第 0 个分量, 定义相等地 `Lev hz = S₀`) 不满射 (`no-ι0`: 第 1 个分量的 $\Omega$-结点不在像里), 所以没有这样的 `RsInv` (`no-sh-ι0`).

```agda
PE : ∀ {X : Set} → (∀ f → X → HB (Lev (jx f))) → Wd K₁ → Set
PE {X} emb w = Σ X (λ a → ∀ f′ → proj₂ (w (inj₂ (hs (jx f′)))) ≡ emb f′ a)

inv→surj : ∀ {X : Set} (emb : ∀ f → X → HB (Lev (jx f))) f (R : RsInv K₁ (PE emb) tp₁ (κH f)) →
  ∀ {w} → PE emb w → ∀ v → Σ X (λ a → emb f a ≡ v)
inv→surj emb f R {w} p v with rsᴵ-P R {w} p v
... | a , h = a , trans (sym (h f)) (rsᴵ-top R {w} {v} p)

embι : ∀ f → H₀ → HB (Lev (jx f))
embι f = ι 0

v₀ : HB (Lev (jx fω))
v₀ = hΩ (1 , tt) (λ _ → hz)

not-ι0 : ∀ a → ¬ (embι fω a ≡ v₀)
not-ι0 hz ()
not-ι0 (hs a) ()
not-ι0 (hl g) ()
not-ι0 (hΩ κ g) ()

no-ι0 : ¬ (∀ v → Σ H₀ (λ a → embι fω a ≡ v))
no-ι0 h = not-ι0 (proj₁ (h v₀)) (proj₂ (h v₀))

-- z₁ 在 PE embι 里 (一切 κH 的界都是 hz = ι 0 hz)
z₁-PE : PE embι z₁
z₁-PE = hz , λ f′ → refl

no-sh-ι0 : ¬ RsInv K₁ (PE embι) tp₁ (κH fω)
no-sh-ι0 R = no-ι0 (inv→surj embι fω R {z₁} z₁-PE)
```

## §6 结论 (按档)

- **[定理, 否定]** **`keepFam-sep`**, **`keepFamH-sep`** (`RsK` 族 + `Keep` ⇒ 分离子; 只用 `rs-top` 与 `keep`); **`no-same-rs`**, **`no-allFam`** (两份可判定地不同的底拷贝共用一个 rs, 或 `AllFam` 的 `inV` 在它们上相同 ⇒ ⊥); **`no-bd-top`** (`RsBd` 的 `rsᵇ-top` 去掉前提 ⇒ ⊥); **`no-sh-ι0`** (`κH fω` 上, 经第 0 个分量编码的共享界没有 `RsInv`).
- **[定理, 盲]** `rsK-moves`, `moves-κH`, `moves-strict` (`RsK` 不管别处); **`all→own`**, **`own→all`** (`AllFam` 与 `OwnFam` 等价); `rsBd-empty`, `rsBd-triv` (`RsBd` 不定 `U` 时盲); `rsInv-empty`; **`sh-same`**, **`sh-all-top`** (共享界的世界里底拷贝分不开, 精确置一个就置了一切); `wS-not-sh`; **`inv→surj`**.
- **[定理, 前提实例]** `rsK∘`, `keep∘`, `decJ→RsK` (条件 `DecJ`), `decJ→keepFam` (条件 `DecJ`), `Psh`, `sh-Psh`, `z₁-Psh`, `z₁-PE`, `wS-0`, `wS-1`.
- **只否定什么.** `Keep` (裸下标律) 与 `RsK` 合用; "一个 rs 服务两个种类" 且 `rs-top` 无前提; `RsBd` 去掉 `rsᵇ-top` 的前提; 共享界经不满射编码. **不否定**: `OwnFam` (每个种类自己的 rs, `rs-top` 无前提, `rs≤` 带前提; 未走通, 条件实例 `decJ→OwnFam` 见 `NegRsOwn`); `RsBd` 与 `RsInv` 本身 (构造一路有实例); 共享界经满射编码的 `κH` 版本.
