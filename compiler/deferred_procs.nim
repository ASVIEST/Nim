import ast, semdata, renderer, lookups, types

proc procBodyDeferredAux(c: PContext, n: PNode, res: var bool, affectsResult, isLast = false): bool =
  # very simple deferred proc checker
  # it cheaper than semProcBody(it calls semExpr)
  var i = 1
  case n.kind:
    of nkStmtList:
      for i, e in n:
        if procBodyDeferredAux(c, e, res, affectsResult, i == n.len - 1):
          break
    of nkAsgn:
      if $n[0] == "result":
        # result = ...
        discard procBodyDeferredAux(c, n[1], res, true)
    
    of nkCall:
      # for generic calls must be full generic param list
      var ident = n[0]
      if ident.kind == nkBracketExpr:
        ident = ident[0]
      var s = lookUp(c, ident)# it can produce error for undeclarated

      if s.ast != nil and s.ast.kind in {nkProcDef, nkFuncDef}:
        let gp = s.ast[genericParamsPos]
        let typ = s.getReturnType

        if (gp.isGenericParams or typ.kind == tyAnything) and n[0].kind == nkIdent and (affectsResult or isLast):
          # genericProc()
          res = true
                
        elif typ != nil and not isLast:
          res = false
          result = true
          return
    else:
      discard

proc procBodyDeferred*(c: PContext, n: PNode): bool =
  discard procBodyDeferredAux(c, n, result)
