
project(TSPASS C)

SET(BASE_SRC 
	clause.c
	context.c
	eml.c
	flags.c
	foldfg.c
	kbo.c
	list.c
	memory.c
	misc.c
	options.c
	order.c
	rpos.c
	sharing.c
	st.c
	stack.c
	strings.c
	subst.c
	symbol.c
	term.c
	unify.c
	version.h)

SET(FLEX_FLAGS "-Ce")

ADD_FLEX_FILE(BASE_SRC iascanner.l ${FLEX_FLAGS} "ia_")
ADD_FLEX_FILE(BASE_SRC dfgscanner.l ${FLEX_FLAGS} "dfg_")

ADD_BISON_FILE(BASE_SRC iaparser.y "ia_")
ADD_BISON_FILE(BASE_SRC dfgparser.y "dfg_")

SET(ALARM_SRC
	alarm.c)

SET(TSPASS_SRC
	${BASE_SRC}
	${ALARM_SRC}
	analyze.c
	clock.c
	closure.c
	cnf.c
	component.c
	condensing.c
	defs.c
	doc-proof.c
	graph.c
	hash.c
	hasharray.c
	partition.c
  proof.c
	proofcheck.c
	ras.c
	renaming.c
	resolution.c
	rules-inf.c
	rules-red.c
	rules-sort.c
	rules-split.c
	rules-ur.c
	search.c
	sort.c
	subsumption.c
	table.c
	tableau.c
	terminator.c
	tl.c
	top.c
	vector.c)

ADD_EXECUTABLE(tspass ${TSPASS_SRC})

IF(NOT CMAKE_BUILD_TYPE)
  SET(CMAKE_BUILD_TYPE "Release")
ENDIF(NOT CMAKE_BUILD_TYPE)

SET(GENERAL_C_FLAGS "-std=gnu99 -Wall -pedantic -m32")

SET(CMAKE_C_FLAGS "${GENERAL_C_FLAGS}")
SET(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE}")
SET(CMAKE_C_FLAGS_MINSIZEREL "${CMAKE_C_FLAGS_MINSIZEREL}")
SET(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -DCHECK=1 -DCHECK_STRSKOLEM=1")
SET(CMAKE_C_FLAGS_RELWITHDEBINFO "${CMAKE_C_FLAGS_RELWITHDEBINFO} -DCHECK=1 -DCHECK_STRSKOLEM=1")

# add the math library
TARGET_LINK_LIBRARIES(tspass m)

INSTALL(PROGRAMS ${CMAKE_CURRENT_BINARY_DIR}/tspass DESTINATION bin)
