# test using coq8.3

test:	testCommon v8only cvsonly
	echo "everything's ok (hasta ahora)"



# files compatible with both CVS and pl2
testCommon : 
	(cd autotac/SRC;  make clean; make all)
	(cd co-inductifs/SRC; make clean;  make all)
	(cd depprod/SRC;make clean;  make all)
	(cd everyday/SRC; make clean; make all)
	(cd extraction/SRC; make clean; make all)
	(cd horizon/SRC; make clean;  make all)
	(cd induc-fond/SRC; make clean; make all)
	(cd inductive-prop-chap/SRC;make clean;  make all)
	(cd modules/SRC;make clean;  make all)
	(cd progav/SRC; make clean; make all)
	(cd propproof/SRC; make clean; make all)
	(cd searchtrees/SRC; make clean;  make all)
	(cd specprog/SRC; make clean; make all)
	(cd structinduct/SRC; make clean; make all)
	(cd gen-rec/SRC; make clean; make all)
	(cd reflection/SRC; make clean; make all)
	(cd newstuff/SRC; make clean; make all)



clean : 
	(cd autotac/SRC;  make clean)
	(cd co-inductifs/SRC; make clean)
	(cd depprod/SRC;make clean)
	(cd everyday/SRC; make clean)
	(cd extraction/SRC; make clean)
	(cd horizon/SRC; make clean)
	(cd induc-fond/SRC; make clean)
	(cd inductive-prop-chap/SRC; make clean)
	(cd modules/SRC;make clean)
	(cd progav/SRC; make clean)
	(cd propproof/SRC; make clean)
	(cd searchtrees/SRC; make clean)
	(cd specprog/SRC; make clean)
	(cd structinduct/SRC; make clean)
	(cd gen-rec/SRC; make clean)
	(cd reflection/SRC; make clean)
	(cd newstuff/SRC; make clean)
	(cd newstuff/CVSONLY; make clean)
	(cd newstuff/V8ONLY; make clean)

# files compatible only with coq CVS

cvsonly :
	(cd newstuff/CVSONLY; make all)
	(cd induc-fond/SRC; make -f makeCVS clean; make -f makeCVS all)

# files compatible only with coq V8pl2

v8only:
	(cd newstuff/V8ONLY; make clean; make all)
	(cd induc-fond/SRC; make -f makev8 clean; make -f makev8 all)
