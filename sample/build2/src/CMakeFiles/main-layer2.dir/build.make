# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.5

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2

# Include any dependencies generated for this target.
include src/CMakeFiles/main-layer2.dir/depend.make

# Include the progress variables for this target.
include src/CMakeFiles/main-layer2.dir/progress.make

# Include the compile flags for this target's objects.
include src/CMakeFiles/main-layer2.dir/flags.make

src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o: src/CMakeFiles/main-layer2.dir/flags.make
src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o: ../src/main-layer2.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o"
	cd /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src && /usr/bin/c++   $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/main-layer2.dir/main-layer2.cpp.o -c /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/src/main-layer2.cpp

src/CMakeFiles/main-layer2.dir/main-layer2.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/main-layer2.dir/main-layer2.cpp.i"
	cd /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/src/main-layer2.cpp > CMakeFiles/main-layer2.dir/main-layer2.cpp.i

src/CMakeFiles/main-layer2.dir/main-layer2.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/main-layer2.dir/main-layer2.cpp.s"
	cd /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/src/main-layer2.cpp -o CMakeFiles/main-layer2.dir/main-layer2.cpp.s

src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.requires:

.PHONY : src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.requires

src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.provides: src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.requires
	$(MAKE) -f src/CMakeFiles/main-layer2.dir/build.make src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.provides.build
.PHONY : src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.provides

src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.provides.build: src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o


# Object files for target main-layer2
main__layer2_OBJECTS = \
"CMakeFiles/main-layer2.dir/main-layer2.cpp.o"

# External object files for target main-layer2
main__layer2_EXTERNAL_OBJECTS =

src/main-layer2: src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o
src/main-layer2: src/CMakeFiles/main-layer2.dir/build.make
src/main-layer2: depends/libsnark/libsnark/libsnark.a
src/main-layer2: depends/libsnark/depends/libff/libff/libff.a
src/main-layer2: /usr/lib/x86_64-linux-gnu/libgmp.so
src/main-layer2: /usr/lib/x86_64-linux-gnu/libgmp.so
src/main-layer2: /usr/lib/x86_64-linux-gnu/libgmpxx.so
src/main-layer2: depends/libsnark/depends/libzm.a
src/main-layer2: src/CMakeFiles/main-layer2.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable main-layer2"
	cd /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/main-layer2.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
src/CMakeFiles/main-layer2.dir/build: src/main-layer2

.PHONY : src/CMakeFiles/main-layer2.dir/build

src/CMakeFiles/main-layer2.dir/requires: src/CMakeFiles/main-layer2.dir/main-layer2.cpp.o.requires

.PHONY : src/CMakeFiles/main-layer2.dir/requires

src/CMakeFiles/main-layer2.dir/clean:
	cd /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src && $(CMAKE_COMMAND) -P CMakeFiles/main-layer2.dir/cmake_clean.cmake
.PHONY : src/CMakeFiles/main-layer2.dir/clean

src/CMakeFiles/main-layer2.dir/depend:
	cd /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2 && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/src /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2 /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src /home/ych/go/src/github.com/weikengchen/libsnark_sample/sample/build2/src/CMakeFiles/main-layer2.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/CMakeFiles/main-layer2.dir/depend

