cmake_minimum_required(VERSION 2.6)

MACRO(FIND_FLEX)
	FIND_PROGRAM(FLEX_BINARY flex)
	IF(NOT FLEX_BINARY)
 		MESSAGE(FATAL_ERROR "Could not find \"flex\"!")
	ELSE(NOT FLEX_BINARY)
 		MESSAGE(STATUS "Flex binary found under ${FLEX_BINARY}.")
	ENDIF(NOT FLEX_BINARY)
ENDMACRO(FIND_FLEX)

MACRO(FIND_BISON)
	FIND_PROGRAM(BISON_BINARY bison)
	IF(NOT BISON_BINARY)
 		MESSAGE(FATAL_ERROR "Could not find \"bison\"!")
	ELSE(NOT BISON_BINARY)
 		MESSAGE(STATUS "Bison binary found under ${BISON_BINARY}.")
	ENDIF(NOT BISON_BINARY)
ENDMACRO(FIND_BISON)


FIND_FLEX()
FIND_BISON()

MACRO(ADD_FLEX_FILE SRC FLEX_FILE FLEX_FLAGS FLEX_PREFIX)
	GET_FILENAME_COMPONENT(_ABS_SRC ${CMAKE_CURRENT_SOURCE_DIR}/${FLEX_FILE} ABSOLUTE)
	GET_FILENAME_COMPONENT(_BASENAME ${_ABS_SRC} NAME_WE)

	SET(_DEST ${CMAKE_CURRENT_BINARY_DIR}/${_BASENAME}.c)
	SET(_FLEX_PREFIX s)

	IF(FLEX_PREFIX)
		SET(_FLEX_PREFIX "-P${FLEX_PREFIX}")
	ENDIF(FLEX_PREFIX)

	ADD_CUSTOM_COMMAND(OUTPUT ${_DEST}
			COMMAND ${FLEX_BINARY} ARGS ${FLEX_FLAGS} -P${FLEX_PREFIX} -o${_DEST} ${_ABS_SRC}
			DEPENDS ${_ABS_SRC}
			COMMENT "Invoking Flex for ${_ABS_SRC}.")

	SET(${SRC} ${${SRC}} ${_DEST})

	INCLUDE_DIRECTORIES(${CMAKE_CURRENT_SOURCE_DIR})
ENDMACRO(ADD_FLEX_FILE)

MACRO(ADD_BISON_FILE SRC BISON_FILE BISON_PREFIX)
	GET_FILENAME_COMPONENT(_ABS_SRC ${CMAKE_CURRENT_SOURCE_DIR}/${BISON_FILE} ABSOLUTE)
	GET_FILENAME_COMPONENT(_BASENAME ${_ABS_SRC} NAME_WE)

	SET(_DEST ${CMAKE_CURRENT_BINARY_DIR}/${_BASENAME}.c)
	SET(_HEADER_DEST ${CMAKE_CURRENT_BINARY_DIR}/${_BASENAME}.h)

	ADD_CUSTOM_COMMAND(OUTPUT ${_DEST} ${_HEADER_DEST}
			COMMAND ${BISON_BINARY} ARGS -d -p ${BISON_PREFIX} -o ${_DEST} ${_ABS_SRC}
			DEPENDS ${_ABS_SRC}
			COMMENT "Invoking Bison for ${_ABS_SRC}.")

	SET(${SRC} ${${SRC}} ${_DEST})

	INCLUDE_DIRECTORIES(${CMAKE_CURRENT_SOURCE_DIR})
ENDMACRO(ADD_BISON_FILE)

ADD_SUBDIRECTORY(src)