# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

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
CMAKE_SOURCE_DIR = /home/z29wei/mmz529

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/z29wei/mmz529/cmake-build-debug-eceubuntu

# Include any dependencies generated for this target.
include CMakeFiles/prjece650.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/prjece650.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/prjece650.dir/flags.make

CMakeFiles/prjece650.dir/prjece650.cpp.o: CMakeFiles/prjece650.dir/flags.make
CMakeFiles/prjece650.dir/prjece650.cpp.o: ../prjece650.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/z29wei/mmz529/cmake-build-debug-eceubuntu/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/prjece650.dir/prjece650.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/prjece650.dir/prjece650.cpp.o -c /home/z29wei/mmz529/prjece650.cpp

CMakeFiles/prjece650.dir/prjece650.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/prjece650.dir/prjece650.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/z29wei/mmz529/prjece650.cpp > CMakeFiles/prjece650.dir/prjece650.cpp.i

CMakeFiles/prjece650.dir/prjece650.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/prjece650.dir/prjece650.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/z29wei/mmz529/prjece650.cpp -o CMakeFiles/prjece650.dir/prjece650.cpp.s

# Object files for target prjece650
prjece650_OBJECTS = \
"CMakeFiles/prjece650.dir/prjece650.cpp.o"

# External object files for target prjece650
prjece650_EXTERNAL_OBJECTS =

prjece650: CMakeFiles/prjece650.dir/prjece650.cpp.o
prjece650: CMakeFiles/prjece650.dir/build.make
prjece650: minisat/libminisat.a
prjece650: /usr/lib/x86_64-linux-gnu/libz.so
prjece650: CMakeFiles/prjece650.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/z29wei/mmz529/cmake-build-debug-eceubuntu/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable prjece650"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/prjece650.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/prjece650.dir/build: prjece650

.PHONY : CMakeFiles/prjece650.dir/build

CMakeFiles/prjece650.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/prjece650.dir/cmake_clean.cmake
.PHONY : CMakeFiles/prjece650.dir/clean

CMakeFiles/prjece650.dir/depend:
	cd /home/z29wei/mmz529/cmake-build-debug-eceubuntu && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/z29wei/mmz529 /home/z29wei/mmz529 /home/z29wei/mmz529/cmake-build-debug-eceubuntu /home/z29wei/mmz529/cmake-build-debug-eceubuntu /home/z29wei/mmz529/cmake-build-debug-eceubuntu/CMakeFiles/prjece650.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/prjece650.dir/depend
