# -*- coding: utf-8 -*-
"""直接树版本，计入其内部View与FGH；与旧高闭项同口径执行切片。

旧新HTML分别取成功轮，所有旧源保持只读。这里只是语法依赖近似，
不以低于1513的执行计数代替成品审核或新值证明。
"""
import os
driver = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'locslice_treeemit.py')
with open(driver, encoding='utf-8') as stream:
    code = stream.read()
code = code.replace("A + 'TreeEmitBuildClosed'", "A + 'TotalOrbitNative'")
code = code.replace("['closed', 'closed-legal', 'fgh']", "['closed', 'closed-view', 'fgh']")
code = code.replace("def sliced(roots):", "new_roots += [('OCF.Free.TotalOrbitRun', 'run'), ('OCF.Free.NativeBrouwer', 'view')]\n\ndef sliced(roots):")
exec(compile(code, driver, 'exec'), {'__file__': driver, '__name__': '__main__'})
