# 公共变换: 把单种类主线 (HtFeedTree/HtFeedFold) 上的 MonoPort/HtCrossV 文件克隆到两种种类 (HtTowerFTree/HtTowerFFold)
# 只改世界的类型与序 (A, ⊲ ↦ Wd₂, ≤ʷ), 高度的类型 (H ↦ Ht), 模块参数 (多一个 oΛ), Int 的多一个参数, 数据树多一个构造子 nμ.
# 证明逐句不变. 被 mk_tpport.py 调用.
import re

ID = r"[\w′'₀₁₂₃₄₅₆₇₈₉ᵢⱼ⁺]"

def tok(s):
    return r"(?<!" + ID + r")" + re.escape(s) + r"(?!" + ID + r")"

def sub_tok(code, old, new):
    return re.sub(tok(old), lambda m: new, code)

WORLDS = ["W₀′", "W₀", "W′", "W₁", "W₂", "W", "V₀", "V′", "V₁", "V₂", "V₃", "V", "m"]

def blocks(src):
    """源文件里全部 agda 代码块 (含围栏)."""
    out = []
    i = 0
    while True:
        a = src.find("```agda", i)
        if a < 0:
            break
        b = src.find("\n```", a + 7)
        out.append(src[a:b + 4])
        i = b + 4
    return out

def strip_imports(first):
    """去掉第一块里的选项、导入、模块头 (含续行), 留下其余定义."""
    lines = first.split("\n")
    keep = []
    in_imp = False
    for ln in lines:
        s = ln.strip()
        if s.startswith("{-#") or s.startswith("open import") or s.startswith("import ") or s.startswith("module OCF."):
            in_imp = True
            continue
        if in_imp and (ln.startswith("  ") and not s == ""):
            continue
        in_imp = False
        keep.append(ln)
    return "\n".join(keep)

def common(code):
    # 世界
    code = code.replace("C.⊲-tr", "≤tr")
    code = code.replace("C.self", "≤rf")
    code = code.replace("⊲ᴴ↑", "⊲ᴮ↑").replace("z⊲ᴴ", "z⊲ᴮ").replace("⊲ᴴ-tr", "⊲ᴮ-tr").replace("S→⊲ᴴ", "S→⊲")
    code = code.replace("cmpH", "cmpB")
    for w in WORLDS:
        code = re.sub(r"(?<!" + ID + r")Lg " + re.escape(w) + r"(?!" + ID + r")", "LgW₂ " + w, code)
    for a in WORLDS + ["tw V"]:
        for b in WORLDS:
            code = re.sub(r"(?<!" + ID + r")" + re.escape(a) + r" ⊲ " + re.escape(b) + r"(?!" + ID + r")",
                          a + " ≤ʷ " + b, code)
    code = code.replace("{W : A}", "{W : Wd₂}").replace("(W : A)", "(W : Wd₂)").replace("{m : A}", "{m : Wd₂}")
    # 高度
    code = sub_tok(code, "LgH", "LgB")
    code = sub_tok(code, "H", "Ht")
    code = re.sub(r"\(hΩ (" + ID + r"+)\)", r"(hΩ _ \1)", code)
    code = re.sub(r"\{t = hΩ (" + ID + r"+)\}", r"{t = hΩ _ \1}", code)
    code = re.sub(r"\{hΩ (" + ID + r"+)\}", r"{hΩ _ \1}", code)
    # 一步
    for p in ["P", "Q", "F₁", "F₂"]:
        code = code.replace(p + ".Step ", p + ".Stp ")
    # 模块参数多一个 oΛ
    code = code.replace("Λ lΛ lW t₀", "Λ lΛ oΛ lW t₀")
    # 数据树多一个构造子 nμ: 每个 nκ 的空子句后面加一句
    out = []
    for ln in code.split("\n"):
        out.append(ln)
        if re.search(r"\(nκ \(\) ", ln):
            out.append(re.sub(r"\(nκ \(\) ", "(nμ () ", ln))
    code = "\n".join(out)
    return code

def build(src, header, imports, extra=None, drop=None, keep_blocks=None):
    bs = blocks(src)
    if keep_blocks is not None:
        bs = [bs[i] for i in keep_blocks]
    first = strip_imports(bs[0])
    body = [first] + bs[1:]
    code = "\n".join(body)
    if drop:
        for d in drop:
            assert d in code, ("drop", d[:60])
            code = code.replace(d, "")
    code = common(code)
    if extra:
        for old, new in extra:
            assert old in code, ("extra", old[:80])
            code = code.replace(old, new)
    # 第一块: 换成新的导入
    code = code.replace("```agda\n", "```agda\n" + imports + "\n", 1)
    return header + "\n" + code + "\n"
