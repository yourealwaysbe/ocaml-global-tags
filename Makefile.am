
ACLOCAL_AMFLAGS= -I m4

bin_SCRIPTS=ocaml_tags$(EXEEXT) ogtags$(EXEEXT)
dist_pkgdata_DATA=gtags_ocaml.conf ocaml_tags.cmo
EXTRA_DIST=ocaml_tags.run ogtags.run

do_subst = sed -e 's,[@]pkgdatadir[@],$(pkgdatadir),g' \
               -e 's,[@]exeext[@],$(EXEEXT),g'		          

     

ocaml_tags$(EXEEXT): 
	$(do_subst) < ocaml_tags.run > $@

ogtags$(EXEEXT): 
	$(do_subst) < ogtags.run > $@

.ml.cmo:
	ocamlc -c -I +camlp4 $^ -o $@

CLEANFILES=*.cmi *.cmo $(bin_SCRIPTS)
