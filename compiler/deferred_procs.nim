import ast, semdata, lookups, types
type
  DeferredProcFlag = enum
    dpAffectsResult
    dpIsLast

proc procBodyDeferredAux(c: PContext, n: PNode, res: var bool, flags: set[DeferredProcFlag] = {}): bool =
  # very simple deferred proc checker
  # it cheaper than semProcBody(it calls semExpr)
  proc isDeferredProc(n: PNode): bool =
    discard procBodyDeferredAux(c, n[bodyPos], result, flags + {dpAffectsResult})

  template earlyExit: untyped =
    return true

  var i = 1
  case n.kind:
    of nkStmtList:
      for i, e in n:
        if procBodyDeferredAux(
          c, e, res, 
          flags + (
            if i == n.len - 1:
              {dpAffectsResult, dpIsLast}
            else:
              {dpAffectsResult}
          )
        ):
          break
    of nkAsgn:
      if n[0].ident.s == "result":
        # result = ...
        discard procBodyDeferredAux(c, n[1], res, flags + {dpAffectsResult})
    
    of nkCall:
      # for generic calls must be full generic param list
      var ident = n[0]
      if ident.kind == nkBracketExpr:
        ident = ident[0]
      var s = lookUp(c, ident)# it can produce error for undeclarated

      if (let procDef = s.ast; procDef) != nil and procDef.kind in {nkProcDef, nkFuncDef}:
        let gp = procDef[genericParamsPos]
        let typ = s.getReturnType
        let genericOrDeferred =
          gp.isGenericParams or
          (typ.kind == tyAnything and isDeferredProc(procDef))

        if genericOrDeferred and n[0].kind == nkIdent and flags * {dpAffectsResult, dpIsLast} != {}:
          # generic or deferred proc
          res = true
                
        elif typ != nil and dpIsLast notin flags:
          res = false
          earlyExit
    else:
      discard

proc procBodyDeferred*(c: PContext, n: PNode): bool =
  discard procBodyDeferredAux(c, n, result)
