make TOPFILE=test000
./test000.opt >> test000.log
diff test000.log orig/test000.log
