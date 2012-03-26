

AC_INIT([ocaml_tags],[1.0])
AM_INIT_AUTOMAKE

AC_PROG_CC

AC_PROG_OCAML
if test "$OCAMLC" = "no"; then
  AC_MSG_ERROR([You must install the OCaml compiler])
fi

ocaml_version_error="OCaml must be at least version 3.10."
ocaml_maj_version=`echo $OCAMLVERSION | ${AWK} -F . "{print \\$1}"`
ocaml_min_version=`echo $OCAMLVERSION | ${AWK} -F . "{print \\$2}"`

if test $ocaml_maj_version -lt 3; then
    AC_MSG_ERROR([$ocaml_version_error])
fi
 
if test $ocaml_maj_version -eq 3 && test $ocaml_min_version -lt 10; then
    AC_MSG_ERROR([$ocaml_version_error])
fi
 

AC_PROG_CAMLP4
if test "$CAMLP4O" = "no"; then
  AC_MSG_ERROR([You must install camlp4o])
fi

AC_CHECK_PROG([GTAGS],[gtags],[yes],[no])
if test "$GTAGS" = "no"; then
  AC_MSG_WARN([gtags was not found -- ogtags will not work without it.])
fi

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
