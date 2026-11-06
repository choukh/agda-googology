# NegRaise (一): `RaiseA` 不能再有的性质, 与接口盲在哪里

> 不含记号. 入口 [NegRaise](NegRaise.lagda.md). 对着接口 [RaiseIf](RaiseIf.lagda.md) ("接口定稿 2026-11-05 (主审写, 首次编译通过后定稿)", 变更记录: 无) 写, 导入它, 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 本篇的否定定理都落到 `HtTowerNeg.no-joinA` (偶数列与奇数列的 ℕ-极限没有合法的字面公共上界) 上: 每条额外的性质都让 $R$ 的某个输出同时含 `alim evA` 与 `alim odA`.
>
> 1. **`no-mono0`**: `RaiseA` 加 "对 $a$ 单调, 只要在 $0$ 处" ($R\,0\,v\lhd R\,a\,v$) 矛盾. 所以一般的 "对 $a$ 单调" 也矛盾 (`no-mono-a`).
> 2. **`no-cont0`**: `RaiseA` 加 "在 $a$ 的 ℕ-极限处, 首项的输出是极限的输出的第一位置" ($R\,(f\,0)\,v\lhd R\,(\mathrm{alim}\,f)\,v$) 矛盾. 这否定对 $a$ 的那种连续性 ($R\,(\mathrm{alim}\,f)\,v$ 由各 $R\,(f\,n)\,v$ 组成, 而且含 $R\,(f\,0)\,v$).
> 3. **`no-flip`**: `RaiseA` 加 "$R\,v\,a\lhd R\,a\,v$" (对称的弱形) 矛盾.
> 4. **`no-tp-rs-upAll`**: 在接口 §3 的积世界上用 `upAll` 做 `FBA` 式的回灌 (读分量 $i_0$): `rs≤`, `rsLg` 与带前提的 `tp-rs` 都由 `RaiseA` 给出 (`rs≤-upAll`, `rsLg-upAll`, `tp-rs-cond`), **无前提的 `tp-rs`** 与 `RaiseA` 矛盾. 所以 "一起升" 接到 `GenFoldIf.FBA` 上, 必须把 `tp-rs` 改成带前提 `tpA w ⊲ v` 的形状. 否定部分与构造一路的 `RaiseCFba.no-fba-upAll` 是同一结论 (那里在 `SA` 上对一切 $G$, 不要 `RaiseA`; 这里对一切下标类型 $I$, 对 `RaiseA` 的 $R$), 两路各自写出, 以那里的为主; 本篇新的只是正面的三条.
> 5. **盲 (`raise-up`, `inflate`, `head-suc`, `head-lim`)**: 三条律只给下界, 对输出向上封闭: 任何 `RaiseA` 的输出外面再包一层合法的东西, 仍是 `RaiseA`. 于是若有一个 `RaiseA`, 就有输出头恒为 `asuc` 的, 也有输出头恒为 `alim` 的. 输出的有限的头形状不被律决定.
>
> 每条否定的前提实例在 §5.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegRaiseBnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerNeg using (evA; odA; Lg-evA; Lg-odA; no-joinA)
open import OCF.Align.RaiseIf using (RaiseA; R; R-lo; R-hi; R-lg; module ProdA)
```

## §0 一个公共的出口

只要某个合法的 $L$ 同时以 `alim evA` 与 `alim odA` 为第一位置, 就撞 `no-joinA`.

```agda
EV OD : A
EV = alim evA
OD = alim odA

both : ∀ {L} → Lg L → EV ⊲ L → OD ⊲ L → ⊥
both {L} l p q = no-joinA (L , l , p , q)
```

## §1 对 $a$ 单调 (只要在 $0$ 处)

$0\lhd v$ 恒成立, 所以 `R-hi` 给 $v\lhd R\,0\,v$; 单调把它搬进 $R\,a\,v$; `R-lo` 又给 $a\lhd R\,a\,v$.

```agda
Mono0 : RaiseA → Set
Mono0 ρ = ∀ {a v} → Lg a → Lg v → R ρ azero v ⊲ R ρ a v

no-mono0 : ∀ ρ → ¬ Mono0 ρ
no-mono0 ρ m = both (R-lg ρ Lg-evA Lg-odA) (R-lo ρ Lg-evA Lg-odA)
  (⊲-tr (R-hi ρ tt Lg-odA (z⊲ OD)) (m Lg-evA Lg-odA))

MonoA : RaiseA → Set
MonoA ρ = ∀ {a a′ v} → Lg a → Lg a′ → Lg v → a ⊲ a′ → R ρ a v ⊲ R ρ a′ v

no-mono-a : ∀ ρ → ¬ MonoA ρ
no-mono-a ρ m = no-mono0 ρ (λ {a} la lv → m tt la lv (z⊲ a))
```

## §2 在 $a$ 的 ℕ-极限处含首项的输出

`evA 0 = azero`, 所以这是 §1 在 $a=$ `alim evA` 处的特例.

```agda
Cont0 : RaiseA → Set
Cont0 ρ = ∀ {f v} → Lg (alim f) → Lg v → R ρ (f 0) v ⊲ R ρ (alim f) v

no-cont0 : ∀ ρ → ¬ Cont0 ρ
no-cont0 ρ c = both (R-lg ρ Lg-evA Lg-odA) (R-lo ρ Lg-evA Lg-odA)
  (⊲-tr (R-hi ρ tt Lg-odA (z⊲ OD)) (c Lg-evA Lg-odA))
```

## §3 对称的弱形

```agda
Flip : RaiseA → Set
Flip ρ = ∀ {a v} → Lg a → Lg v → R ρ v a ⊲ R ρ a v

no-flip : ∀ ρ → ¬ Flip ρ
no-flip ρ fl = both (R-lg ρ Lg-evA Lg-odA) (R-lo ρ Lg-evA Lg-odA)
  (⊲-tr (R-lo ρ Lg-odA Lg-evA) (fl Lg-evA Lg-odA))
```

## §4 积世界上的 `upAll` 与 `FBA` 的 `tp-rs`

接口 §3: 一族分量 $W:I\to A$, 一起升成 $i\mapsto R\,(W\,i)\,v$. 读分量 $i_0$ 作 `tpA`. `GenFoldIf.FBA` 的四条律在这里的对应:

```agda
module UpAll (I : Set) (i₀ : I) where
  open ProdA I

  -- rs≤: 不要前提, 由 R-lo
  rs≤-upAll : ∀ ρ {W v} → LgP W → Lg v → W ≤ᴾ upAll ρ W v
  rs≤-upAll ρ lW lv i = R-lo ρ (lW i) lv

  -- rsLg: 由 R-lg
  rsLg-upAll : ∀ ρ {W v} → LgP W → Lg v → LgP (upAll ρ W v)
  rsLg-upAll ρ lW lv i = R-lg ρ (lW i) lv

  -- 带前提的 tp-rs: 由 R-hi
  tp-rs-cond : ∀ ρ {W v} → LgP W → Lg v → W i₀ ⊲ v → v ⊲ upAll ρ W v i₀
  tp-rs-cond ρ lW lv p = R-hi ρ (lW i₀) lv p

  -- 无前提的 tp-rs: 矛盾
  TpRs : RaiseA → Set
  TpRs ρ = ∀ {W v} → LgP W → Lg v → v ⊲ upAll ρ W v i₀

  no-tp-rs-upAll : ∀ ρ → ¬ TpRs ρ
  no-tp-rs-upAll ρ t = both (R-lg ρ Lg-evA Lg-odA) (R-lo ρ Lg-evA Lg-odA)
    (t {λ _ → EV} {OD} (λ _ → Lg-evA) Lg-odA)
```

## §5 前提实例: 去掉一条律, 其余可满足

两个平凡的算子 (接口文件头已说): `Rfst` ($R\,a\,v=a$) 满足 `R-lo`, `R-lg`; `Rsnd` ($R\,a\,v=v$) 满足 `R-hi`, `R-lg`. 下面逐条验证, 它们也满足 §1 到 §4 各自加的性质. 所以 §1 到 §4 的每条否定都只在三条律**同时**成立时才起作用; 三条律本身经典地可满足 (构造一路 `RaiseCBd.dec→Raise`, 条件: 子项关系可判定), 本篇在 [NegRaiseFin](NegRaiseFin.lagda.md) 给出它的构造性的部分实例.

```agda
Rfst Rsnd : A → A → A
Rfst a v = a
Rsnd a v = v

fst-lo : ∀ {a v} → a ⊲ Rfst a v
fst-lo = C.self

snd-hi : ∀ {a v} → a ⊲ v → v ⊲ Rsnd a v
snd-hi _ = C.self

-- §1, §2: Rfst 与 Rsnd 都对 a 单调, 都含首项
fst-mono0 : ∀ {a v} → Rfst azero v ⊲ Rfst a v
fst-mono0 {a} = z⊲ a

snd-mono0 : ∀ {a v} → Rsnd azero v ⊲ Rsnd a v
snd-mono0 = C.self

fst-mono-a : ∀ {a a′ v} → a ⊲ a′ → Rfst a v ⊲ Rfst a′ v
fst-mono-a p = p

fst-cont0 : ∀ {f v} → Rfst (f 0) v ⊲ Rfst (alim f) v
fst-cont0 = C.lim 0 C.self

snd-cont0 : ∀ {f v} → Rsnd (f 0) v ⊲ Rsnd (alim f) v
snd-cont0 = C.self

-- §3: 常值 0 满足 Flip 与 R-lg; Rsnd 满足 Flip 当且仅当 a ⊲ v (这里只给常值)
Rzero : A → A → A
Rzero a v = azero

zero-flip : ∀ {a v} → Rzero v a ⊲ Rzero a v
zero-flip = C.self

-- §4: Rsnd 给出无前提的 tp-rs (它不满足 rs≤)
module _ (I : Set) (i₀ : I) where
  open ProdA I
  snd-tp-rs : ∀ (W : I → A) v → v ⊲ Rsnd (W i₀) v
  snd-tp-rs W v = C.self
```

## §6 盲: 律对输出向上封闭

```agda
raise-up : ∀ ρ (R′ : A → A → A) →
  (∀ {a v} → Lg a → Lg v → R ρ a v ⊲ R′ a v) → (∀ {a v} → Lg a → Lg v → Lg (R′ a v)) → RaiseA
raise-up ρ R′ up lg = record
  { R = R′
  ; R-lo = λ la lv → ⊲-tr (R-lo ρ la lv) (up la lv)
  ; R-hi = λ la lv p → ⊲-tr (R-hi ρ la lv p) (up la lv)
  ; R-lg = lg }

inflate : RaiseA → (F : A → A) → (∀ x → x ⊲ F x) → (∀ {x} → Lg x → Lg (F x)) → RaiseA
inflate ρ F up lg = raise-up ρ (λ a v → F (R ρ a v)) (λ _ _ → up _) (λ la lv → lg (R-lg ρ la lv))

-- 头恒为后继
IsSuc IsLim : A → Set
IsSuc x = Σ A (λ y → x ≡ asuc y)
IsLim x = Σ (ℕ → A) (λ g → x ≡ alim g)

head-suc : RaiseA → Σ RaiseA (λ ρ′ → ∀ a v → IsSuc (R ρ′ a v))
head-suc ρ = inflate ρ asuc (λ x → C.suc C.self) (λ l → l) , λ a v → R ρ a v , refl

-- 头恒为 ℕ-极限 (常值列, 合法)
cst : A → A
cst x = alim (λ _ → x)

head-lim : RaiseA → Σ RaiseA (λ ρ′ → ∀ a v → IsLim (R ρ′ a v))
head-lim ρ = inflate ρ cst (λ x → C.lim 0 C.self) (λ l → (λ _ → C.self) , (λ _ → l)) , λ a v → (λ _ → R ρ a v) , refl
```

## §7 结论 (按档)

- **[定理]** `no-mono0`, `no-mono-a`, `no-cont0`, `no-flip`, `UpAll.no-tp-rs-upAll`: 三条律同时成立时, 这些附加性质都不能有. 都归到 `no-joinA`.
- **[定理]** `UpAll.rs≤-upAll`, `rsLg-upAll`, `tp-rs-cond`: `upAll` 满足 `FBA` 的 `rs≤`, `rsLg` 与带前提的 `tp-rs`.
- **[定理, 前提实例]** §5: 每条附加性质与三条律中的两条可同时满足 (`Rfst`, `Rsnd`, `Rzero`).
- **[定理, 盲]** `raise-up`, `inflate`, `head-suc`, `head-lim`: 律对输出向上封闭; 输出的头形状不被律决定.
- **[判断]** §6 是否定一路没找到 `RaiseA → 非构造原则` 的原因之一: 三条律都是下界, 一个可判定的观察若只读输出 (头形状, 有限深的构造子), 总能被 "外包一层" 改掉. 要泄露信息, 观察得用到输出与别的树的**上界**关系, 而接口不给. 这只是判断, 不是 "不能从 `RaiseA` 推出 WLPO" 的定理.
