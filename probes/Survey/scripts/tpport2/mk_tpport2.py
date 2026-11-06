# 生成 TpPort2 的克隆文件: 单种类主线上 MonoPort8Sim 的两世界互模拟 (§1-§7) 搬到两种种类的折叠 HtTowerFFold 上.
# 用法 (从仓库根): python3 probes/Survey/scripts/tpport2/mk_tpport2.py .
# 公共变换用 probes/Survey/scripts/tpport/tpgen.py (只读, 不改); 这里只把世界变量表加上 m′, U, U′, U₁, U₂
# (MonoPort8Sim 的两世界陈述里出现), 再做逐字替换.
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "tpport"))
import tpgen
from tpgen import build

tpgen.WORLDS = tpgen.WORLDS + ["m′", "U′", "U₁", "U₂", "U"]

root = sys.argv[1]
AL = os.path.join(root, "probes/OCF/Align")

def rd(name):
    return open(os.path.join(AL, name + ".lagda.md")).read()

def wr(name, text):
    open(os.path.join(AL, name + ".lagda.md"), "w").write(text)

OPT = "{-# OPTIONS --safe --without-K --lossy-unification #-}"

SIM_IMP = OPT + """
module OCF.Align.TpPort2Sim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtTowerTy using (HB; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; LgB; ⊲ᴮ↑)
open import OCF.Align.HtTowerFTree renaming (_≤_ to _≤ʷ_)
open import OCF.Align.HtTowerFClosed using (ω⋅)
import OCF.Align.HtTowerFFold as Fold
open import OCF.Align.TpPortSim using (Free; free⊲; outS-inS)
open import OCF.Align.TpPortRun using (module Val)"""

HDR = ("# 两种种类的 Ω-极限一步 (一): 两边世界各自独立的互模拟\n\n"
       "> 入口 [TpPort2](TpPort2.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport2/mk_tpport2.py` 从 "
       "[MonoPort8Sim](MonoPort8Sim.lagda.md) 的 §1–§7 逐字节可重生成. 公共变换用 `probes/Survey/scripts/tpport/tpgen.py` (同 `TpPort` 的克隆): "
       "世界的类型与序 (`A`, `_⊲_` 换成 `Wd₂`, `_≤ʷ_`; `C.self`, `⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, "
       "`LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), `Step` 换名 `Stp`; 世界变量表多 `m′`, `U`, `U′`, `U₁`, `U₂`. 逐字替换: 世界的类型注记 "
       "(`{W W′ : A}` 等) 换成 `Wd₂`; `Two` 多两个实例的 `o₁`, `o₂` (两种种类的折叠要第 1 层是第一位置); `IntE` 多两个 `NZ₁` 搬运参数 "
       "`zz₁`, `zz₂` (两种种类的 `Int` 的字面), 节点一句与 `Ai-E` 的内层多 `NZ₁-S`; 原文的 `no-κE` (只对单种类的 `hΩ g` 写) 去掉, "
       "两种种类的对应在 [TpPort2Cross](TpPort2Cross.lagda.md). 关系没有 `nκ`, `nμ` 的构造子, 所以折叠的 `nκ`, `nμ` 两句不出现. 证明逐句不变.\n"
       ">\n"
       "> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.\n")

def sim():
    src = rd("MonoPort8Sim")
    O1 = "(o₁ : ∀ {w} → hs hz ⊲[ w ] Λ₁)"
    O2 = "(o₂ : ∀ {w} → hs hz ⊲[ w ] Λ₂)"
    drop = [
        "\n-- 边界: 关系没有 nκ 的子句, 所以 Ω-极限层的 Ω_L 不与自己相关 (对一切 g, 一切两个世界)\n"
        "no-κE : ∀ (g : A → H) {W W′} → ¬ Re (hΩ g) (Ωd (hΩ g) {W}) (Ωd (hΩ g) {W′})\n"
        "no-κE g (e⨾ _ ())\n",
    ]
    extra = [
        ("(W W′ : A)", "(W W′ : Wd₂)"),
        ("{W W′ : A}", "{W W′ : Wd₂}"),
        ("{m m′ : A}", "{m m′ : Wd₂}"),
        ("zy₁ zy₂ ", "zy₁ zy₂ zz₁ zz₂ "),
        ("(zy₁ zy₂ zz₁ zz₂ : NZ ly)", "(zy₁ zy₂ : NZ ly) (zz₁ zz₂ : NZ₁ k → NZ₁ ly)"),
        ("Re ly (Int a₁ x₁ q₀ lW zy₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀′ lW′ zy₂ mk₂ u₂ w₂)",
         "Re ly (Int a₁ x₁ q₀ lW zy₁ zz₁ mk₁ u₁ w₁) (Int a₂ x₂ q₀′ lW′ zy₂ zz₂ mk₂ u₂ w₂)"),
        ("(NZ-S R₁) (NZ-S R₂)", "(NZ-S R₁) (NZ-S R₂) (NZ₁-S R₁) (NZ₁-S R₂)"),
        ("(NZ-S r₁) (NZ-S r₂)", "(NZ-S r₁) (NZ-S r₂) (NZ₁-S r₁) (NZ₁-S r₂)"),
        ("module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) (Λ₂ : Ht) (l₂ : LgB Λ₂)",
         "module Two (Λ₁ : Ht) (l₁ : LgB Λ₁) " + O1 + " (Λ₂ : Ht) (l₂ : LgB Λ₂) " + O2),
        ("module F₁ = Fold ω⋅ Λ₁ l₁", "module F₁ = Fold ω⋅ Λ₁ l₁ o₁"),
        ("module F₂ = Fold ω⋅ Λ₂ l₂", "module F₂ = Fold ω⋅ Λ₂ l₂ o₂"),
        ("module V₁ = Val Λ₁ l₁", "module V₁ = Val Λ₁ l₁ o₁"),
        ("module V₂ = Val Λ₂ l₂", "module V₂ = Val Λ₂ l₂ o₂"),
        ("⊲-tr", "≤tr"),
    ]
    wr("TpPort2Sim", build(src, HDR, SIM_IMP, extra, drop=drop, keep_blocks=list(range(8))))

TARGETS = {"sim": sim}

if __name__ == "__main__":
    which = sys.argv[2:] or list(TARGETS)
    for w in which:
        TARGETS[w]()
