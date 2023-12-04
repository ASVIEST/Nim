#
#
#           The Nim Compiler
#        (c) Copyright 2023 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Nir Compiler.

import ".." / ic / [bitabs, rodfiles]
import nirinsts, nirtypes, nirlineinfos, nirfiles, cir
import target_props

proc view(filename: string) =
  let m = load(filename)
  var res = ""
  allTreesToString m.code, m.lit.strings, m.lit.numbers, m.symnames, res
  res.add "\n# TYPES\n"
  nirtypes.toString res, m.types
  echo res

import std / [syncio, parseopt]

proc writeHelp =
  echo """Usage: nirc view|c <file.nir>"""
  quit 0

proc main =
  var inp = ""
  var cmd = ""
  var props = TargetProps(inlineAsmSyntax: GCCExtendedAsm)

  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      if cmd.len == 0: cmd = key
      elif inp.len == 0: inp = key
      else: quit "Error: too many arguments"
    of cmdLongOption, cmdShortOption:
      case key
      of "help", "h": writeHelp()
      of "version", "v": stdout.write "1.0\n"
      of "inlineAsmSyntax", "a":
        if val == "":
          quit "Error: no inline asm syntax specified"
        
        props.inlineAsmSyntax =
          case val:
            of "none": None
            of "gcc-like": GCCExtendedAsm
            of "msvc-like": VisualCPP
            else:
              quit "Error: invalid inline asm syntax. Must be: gcc-like or msvc-like (or none)"

    of cmdEnd: discard
  if inp.len == 0:
    quit "Error: no input file specified"
  case cmd
  of "", "view":
    view inp
  of "c":
    let outp = inp & ".c"
    cir.generateCode inp, outp, props

main()
