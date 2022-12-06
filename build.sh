#!/usr/bin/env bash

# Settings/Utilities
# ------------------

# terminate on error
# this will stop running test cases
#set -e

# error if an variable is referenced before being set
set -u

# set variables
top_dir="$(pwd)"
src_dir="$(pwd)/src"
third_party="$top_dir/3rd_party"
build_dir="$top_dir/.build"

# -------------------
include_dir="$build_dir/include"
lib_dir="$build_dir/lib"

# OS detection
OS_NAME=$(uname -s)

# functionality
# -------------
# shellcheck disable=SC2068
progress() { echo "===== " $@ ; }

build_deps() {
  build_gmp
  build_libsigsegv
  build_libncurses
  build_tecla
  build_libpoly
  build_cudd
  build_buddy

  # build smt solvers
  progress "Prepare SMT solvers"
  build_z3
  build_yices2
  build_cvc4
  # TODO: Change this to cvc5

  # build dependencies for flowstar
  build_mpfr
  build_glpk
  build_gsl

  rm -rf "$build_dir"/lib/*.so*
  rm -rf "$build_dir"/lib/*.dylib*
}

patch_maude() {
  progress "Apply patchings"
  maude_src_dir="$top_dir/Maude"
  patch_src_dir="$top_dir/src/patch"

  patch "$maude_src_dir/configure.ac" < "$patch_src_dir/configure-ac.patch"
  patch "$maude_src_dir/src/Makefile.am" < "$patch_src_dir/makefile-am.patch"
  patch "$maude_src_dir/src/Main/Makefile.am" < "$patch_src_dir/main-makefile-am.patch"
  patch "$maude_src_dir/src/Mixfix/yices2_Bindings.hh" < "$patch_src_dir/mixfix-yices2-bindings-hh.patch"
  patch "$maude_src_dir/src/Mixfix/cvc4_Bindings.hh" < "$patch_src_dir/mixfix-cvc4-bindings-hh.patch"
  patch "$maude_src_dir/src/Mixfix/Makefile.am" < "$patch_src_dir/mixfix-makefile-am.patch"
  patch "$maude_src_dir/src/Mixfix/symbolType.hh" < "$patch_src_dir/mixfix-symbol-type-hh.patch"
  patch "$maude_src_dir/src/Mixfix/specialSymbolTypes.cc" < "$patch_src_dir/mixfix-special-symbol-types-cc.patch"
  patch "$maude_src_dir/src/Mixfix/fancySymbols.cc" < "$patch_src_dir/mixfix-fancy-symbols-cc.patch"
  patch "$maude_src_dir/src/Mixfix/mixfixModule.cc" < "$patch_src_dir/mixfix-mixfix-module-cc.patch"
}

run_test() {
  progress "Run test case"
  maude_bin_dir="$top_dir/Maude/src/Main"
  test_dir="$top_dir/src/tests"

  cp $top_dir/src/smt-check.maude $maude_bin_dir

  cd $test_dir && make && make clean
}

print_test_result(){
  if [ -s $1 ]; then
    # The file is not-empty.
    rm -f $1
    echo -e "$1: fail"
  else
    # The file is empty.
    rm -f $1
    echo -e "$1: success"
  fi
}

# build maude
# TODO: need to update in ubuntu
build_maude() {
  # shellcheck disable=SC2145
  progress "Building Maude $@"
  progress "Copying source files to Maude directory"
  cp -r "$top_dir/src/extension" "$top_dir/Maude/src"
  # cp -r "$top_dir/src/ode" "$top_dir/Maude/src"
  cd "$top_dir/Maude"
  aclocal
  autoconf
  autoheader
  automake --add-missing
  automake

  # need to build first with dynamic options,
  # and then do the static building.
  # maude needs dynamic library for TCP.
  # Bstatic will compile only z3 with libz3.a not libz3.so
  #
  # CXXFLAGS if you need dynamic library linking,
  # you need to add libz3.so to lib dir and remove -pthread option
  #
  # ./configure CXXFLAGS="-std=c++11 -I$include_dir -pthread" \
  #	    LDFLAGS="-L$lib_dir" \
  #	    "$@"
  ./configure CFLAGS="-fPIC" CXXFLAGS="-fPIC -std=c++11 -I$include_dir -pthread" \
      LDFLAGS="-L$lib_dir" \
      BUDDY_LIB="$lib_dir/libbdd.a $lib_dir/libpoly.a $lib_dir/libgmp.a $lib_dir/libcudd.a" \
      TECLA_LIBS="$lib_dir/libtecla.a $lib_dir/libncurses.a" \
      GMP_LIBS="$lib_dir/libgmpxx.a $lib_dir/libgmp.a" \
      LIBSIGSEGV_LIB="$lib_dir/libsigsegv.a" \
    "$@"

  make -s -j4
}

# build maude ode
# static build is needed
build_maude_ode_flowstar() {
  # shellcheck disable=SC2145
  progress "Building Maude ODE $@"
  cd "$top_dir/Maude"
  aclocal
  autoconf
  autoheader
  automake --add-missing
  automake

  # need to build first with dynamic options,
  # and then do the static building.
  # maude needs dynamic library for TCP.
  # Bstatic will compile only z3 with libz3.a not libz3.so
  #
  # CXXFLAGS if you need dynamic library linking,
  # you need to add libz3.so to lib dir and remove -pthread option
  #
  # ./configure CXXFLAGS="-std=c++11 -I$include_dir -pthread" \
  #	    LDFLAGS="-L$lib_dir" \
  #	    "$@"
  ./configure CFLAGS="-fPIC -static" CXXFLAGS="-fPIC -std=c++11 -I$include_dir -pthread" \
      LDFLAGS="-L$lib_dir" \
      LIBS="-lflowstar -lgsl -lglpk -lgslcblas -lmpfr -lgmp" \
      BUDDY_LIB="$lib_dir/libbdd.a $lib_dir/libpoly.a $lib_dir/libgmp.a $lib_dir/libcudd.a" \
      TECLA_LIBS="$lib_dir/libtecla.a $lib_dir/libncurses.a" \
      GMP_LIBS="$lib_dir/libgmpxx.a $lib_dir/libgmp.a" \
      LIBSIGSEGV_LIB="$lib_dir/libsigsegv.a" \
      Z3_LIB="-lz3" \
    "$@"

  make -s -j4
}

build_maude_ode_z3() {
  if [ $OS_NAME == "Darwin" ]; then
    echo "Mac detected"
    build_maude_ode CC=cc CXX=c++ --with-yices2=no --with-z3=yes
  else
    echo "Linux detected"
    build_maude_ode --with-yices2=no --with-z3=yes
  fi
}

build_maude_ode_flowstar() {
  if [ $OS_NAME == "Darwin" ]; then
    echo "Mac detected"
    build_maude_ode_flowstar CC=cc CXX=c++ --with-yices2=no --with-z3=yes
  else
    echo "Linux detected"
    build_maude_ode_flowstar --with-yices2=no --with-z3=yes
  fi
}

# build maude with z3
build_maude_z3() {
  if [ $OS_NAME == "Darwin" ]; then
	  echo "Mac detected"
	  mac_build_maude --with-yices2=no --with-z3=yes
  else
	  echo "Linux detected"
	  build_maude --with-yices2=no --with-z3=yes
  fi
}

# build maude with yices2
build_maude_yices2() {
  #build_z3
  if [ $OS_NAME == "Darwin" ]; then
	  echo "Mac detected"
	  mac_build_maude
  else
	  echo "Linux detected"
	  build_maude
  fi
}

# build maude with cvc4
build_maude_cvc4() {
  if [ $OS_NAME == "Darwin" ]; then
	  echo "Mac detected"
	  mac_build_maude --with-yices2=no --with-cvc4=yes
  else
	  echo "Linux detected"
	  build_maude --with-yices2=no --with-cvc4=yes
  fi
}


build_z3() {
  progress "Building z3 submodules"
  z3_dir=$third_party/z3
  # add z3 dependency
  mkdir -p $build_dir
  mkdir -p "$third_party"
  ( progress "Downloading Z3"
    git clone https://github.com/Z3Prover/z3 "$third_party/z3"
    
    cd "$z3_dir"
    python scripts/mk_make.py --prefix="$build_dir" --staticlib
    cd build
    make -j4
    make install
  )

  rm -rf $build_dir/lib/libz3*.so
  rm -rf $build_dir/lib/libz3*.dylib
}

# assume that gmp, libpoly is installed on system.
# yices2 only use c for compile so you don't need CXXFLAGS or so.
build_yices2() {
  progress "Building Yices"
  # shellcheck disable=SC2086
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Yices2"
    git clone https://github.com/SRI-CSL/yices2 "$third_party/yices2"
    
    cd "$third_party/yices2"
    autoconf
    ./configure CFLAGS="-fPIC -I$include_dir" --prefix="$build_dir" \
                LDFLAGS="-L$lib_dir -lpoly -lgmp" \
                --with-static-gmp="$lib_dir/libgmp.a" --with-static-gmp-include-dir="$include_dir" \
                --with-static-libpoly="$lib_dir/libpoly.a" --with-static-libpoly-include-dir="$include_dir" \
                --enable-mcsat

    make -j4
    make install
  )

  rm -rf $build_dir/lib/libyices*.so*
  rm -rf $build_dir/lib/libyices*.dylib
}

# https://github.com/CVC4/CVC4/issues/2672
# commit f8d6bd369a662620c6295a6098dbf8eced37cc6b
# add --static-binary which causes -lcrt0 error in macOS
# ubuntu build is okay without this option.
#
# depedency : libboost, libtool
# outdated goto cvc5
build_cvc4() {
  progress "Building CVC4"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  (	progress "Downloading CVC4"
    git clone https://github.com/CVC4/CVC4-archived.git "$third_party/cvc4"
    
    cd "$third_party/cvc4"
    git checkout f8d6bd369a662620c6295a6098dbf8eced37cc6b

    ./autogen.sh
    ./contrib/get-antlr-3.4
    ./configure production --prefix="$build_dir" --enable-static --disable-shared \
    LIBS="$lib_dir"/libgmp.a
    
    cd "./builds"

    make -s -j4
    make check
    make install
  )
}

build_cudd() {
  progress "Building Cudd"
  cudd_dir=$third_party/cudd-cudd-3.0.0
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Cudd 3.0.0"
    cudd_name="cudd-3.0.0"
  
    curl -L https://github.com/ivmai/cudd/archive/refs/tags/$cudd_name.tar.gz > "$third_party/$cudd_name.tar.gz"
    tar -xvzf "$third_party/$cudd_name.tar.gz" -C "$third_party"
    rm -rf "$third_party/$cudd_name.tar.gz"
    
    cd "$third_party/cudd-$cudd_name"
    ./configure CFLAGS="-fPIC" --prefix="$build_dir"

    make -j4 check
    make install
  )
}

# build gmp
build_gmp() {
  progress "Building gmp library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading gmp 6.1.2"
    get_gnu "gmp" "6.1.2" "tar.xz"
    cd "$third_party/gmp-6.1.2"
    ./configure --prefix="$build_dir" ABI=64 CFLAGS=-fPIC CPPFLAGS=-DPIC \
		--enable-cxx --enable-alloca --disable-shared --enable-static
          
    make -j4
    make check
    make install
  )
}

# need gmp to build this library
build_mpfr() {
  progress "Building mpfr library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading mpfr 4.1.0"
    get_gnu "mpfr" "4.1.0" "tar.gz"
    cd "$third_party/mpfr-4.1.0"
	  ./configure --prefix="$build_dir" --with-gmp="$build_dir" CC=gcc --disable-shared
	  
    make -j4
    make check
    make install
  )
}

build_glpk() {
  progress "Building glpk library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading glpk 5.0"
    get_gnu "glpk" "5.0" "tar.gz"
    cd "$third_party/glpk-5.0"
    ./configure --prefix="$build_dir" CC=gcc --disable-shared
    	
    make -j4
    make check
    make install
  )
}

build_gsl() {
  progress "Building gsl library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading gsl 2.6"
    get_gnu "gsl" "2.6" "tar.gz"
  	cd "$third_party/gsl-2.6"
    ./configure --prefix="$build_dir" CC=gcc --disable-shared
     	
    make -j4
    make check
    make install
  )
}

#
build_buddy() {
  progress "Building BuDDy library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading BuDDy 2.4"
    buddy_dir="$third_party/buddy-2.4"
    
    curl -L https://sourceforge.net/projects/buddy/files/latest/download > "$buddy_dir.tar.gz" 
    tar -xvzf "$buddy_dir.tar.gz" -C "$third_party"
    rm -rf "$buddy_dir.tar.gz"

    cd "$buddy_dir"
    ./configure --includedir="$include_dir" --libdir="$lib_dir" --disable-shared
    
    make -j4
    make install
  )
}

# build tecla
build_tecla() {
  progress "Building tecla library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Tecla 1.6.3"
    tecla_dir="$third_party/libtecla"
  
    curl -o "$tecla_dir.tar.gz" https://sites.astro.caltech.edu/~mcs/tecla/libtecla-1.6.3.tar.gz
    tar -xvzf "$tecla_dir.tar.gz" -C "$third_party"
    rm -rf "$tecla_dir.tar.gz" 
    
    cd "$tecla_dir"
    ./configure --without-man-pages
    make -j4 LIBDIR="$build_dir"/lib INCDIR="$build_dir"/include TARGETS=normal TARGET_LIBS="static" install_lib install_inc
  )
}

# build libsigsegv
build_libsigsegv() {
  progress "Building libsigsegv library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Libsigsegv 2.12"
    get_gnu "libsigsegv" "2.12" "tar.gz"
    sigsegv_dir="$third_party/libsigsegv-2.12"
    
    cd "$sigsegv_dir"
    ./configure --prefix="$build_dir" --disable-shared --enable-static
    
    make -j4
    make check
    make install
  )
}

# build lib ncurses
# does the firm terminfo-dirs work for mac?
build_libncurses() {
  progress "Building libncurses library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Ncurses 6.1"
    get_gnu "ncurses" "6.1" "tar.gz"
    libncurses_dir="$third_party/ncurses-6.1"
    
    cd "$libncurses_dir"
    ./configure --prefix="$build_dir" --datadir="/usr/share" \
    --with-terminfo-dirs="/usr/lib/share:/lib/terminfo:/etc/terminfo" \
    --with-default-terminfo-dir="/usr/share/terminfo" --with-normal --disable-db-install
    
    make -j4
    make install
  )
}

# build ibex
build_ibex() {
  progress "Building ibexlib library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( cd "$ibex_lib_dir"
    ./waf configure --prefix="$build_dir"
    ./waf install
  )
}

# build libpoly for yices non linear support
build_libpoly() {
  progress "Building libpoly library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Libpoly"
    git clone https://github.com/SRI-CSL/libpoly.git "$third_party/libpoly"
    
    cd "$third_party/libpoly/build"
    cmake .. -DCMAKE_BUILD_TYPE="Release" -DCMAKE_INSTALL_PREFIX="$build_dir" -DGMP_LIBRARY="$lib_dir/libgmp.a" -DGMP_INCLUDE_DIR="$include_dir" -DCMAKE_C_FLAGS="-fPIC"
    make
    make install
  )
}

# --- Prepare

get_gnu() {
  name=$1
  version=$2
  ext=$3
  libname="$name-$version"
  mkdir -p "$third_party"
  curl -o "$third_party/$libname.$ext" https://ftp.gnu.org/gnu/$name/$libname.$ext
  tar -xvf "$third_party/$libname.$ext" -C "$third_party"
  rm -rf "$third_party/$libname.$ext"
}

prepare_maude() {
  git clone git@github.com:SRI-CSL/Maude.git
  patch_maude
}


# Main
# ----

build_command="$1" ; shift
case "$build_command" in
    test)               run_test                  "$@" ;;
    patch)              patch_maude               "$@" ;;
    prep-extra)		    extract_all_dep		      "$@" ;;
    prep-git)		    prep_git		          "$@" ;;
    build-cudd)		    build_cudd		          "$@" ;;
    build-libsigsegv)   build_libsigsegv          "$@" ;;
    build-libncurses)   build_libncurses          "$@" ;;
    build-tecla)        build_tecla               "$@" ;;
    build-gmp)          build_gmp                 "$@" ;;
    build-ibex)         build_ibex                "$@" ;;
    build-libpoly)      build_libpoly             "$@" ;;
    build-dreal3)       build_dreal3              "$@" ;;
    build-z3)           build_z3                  "$@" ;;
    build-yices2)       build_yices2              "$@" ;;
    build-cvc4)		    build_cvc4		          "$@" ;;
    clean)              build_clean               "$@" ;;
    deps)               build_deps                "$@" ;;
    maude)              build_maude               "$@" ;;
    prep-maude)         prepare_maude             "$@" ;;
    mac-maude)          mac_build_maude           "$@" ;;
    maude-ode)          build_maude_ode           "$@" ;;
    maude-ode-z3)       build_maude_ode_z3        "$@" ;;
    maude-ode-flowstar) build_maude_ode_flowstar  "$@" ;;
    maude-z3)           build_maude_z3            "$@" ;;
    maude-z3-debug)     build_maude_z3_debug      "$@" ;;
    maude-yices2)       build_maude_yices2        "$@" ;;
    maude-yices2-debug) build_maude_yices2_debug  "$@" ;;
    maude-dreal3)       build_maude_dreal3_os     "$@" ;;
    maude-cvc4)         build_maude_cvc4          "$@" ;;
    maude-cvc4-debug)   build_maude_cvc4_debug    "$@" ;;
    maude-dreal4)       build_maude_dreal4        "$@" ;;
    *)      echo "
    usage: $0 [clean|deps|tangle]
           $0 maude <options>

    $0 prep-extra:		 extract all needed libraries in '$extra_dir'.
    $0 prep-git:       prepare directories for git
    $0 build-cudd:		 build Cudd library with static option.
    $0 build-libsigsegv:         build libsigsegv library with static option.
    $0 build-libncurses:         build libncurses library with static option.
    $0 build-tecla:              build tecla library with static option.
    $0 build-gmp:                build gmp library with static option.
    $0 build-ibex:               build ibex library with static option.
    $0 build-libpoly:            build libpoly library with static option.
    $0 build-z3:                 build submodule of z3.
    $0 build-yices2:             build submodule of yices2.
    $0 build-yices2-poly:        build submodule of yices2 with non linear option.
    $0 build-cvc4:               build submodule of cvc4.
    $0 clean:                    remove build directory '$build_dir', and call 'make clean'.
    $0 deps:                     clone git submodules and build CVC4.
    $0 maude <options>:          build maude passing <options> to the ./configure step.
    $0 mac-maude <options>:      build maude with mac passing <options> to the ./configure step.
    $0 maude-z3 ...:             build_maude using the z3 git submodule.
    $0 maude-z3-debug ...:       build_maude with debugging mode using the z3 git submodule.
    $0 maude-yices2 ...:         build_maude using the yices2 git submodule.
    $0 maude-yices2-debug ...:   build_maude with debugging mode using the yices2 git submodule.
    $0 maude-cvc4 ...:           build_maude using the cvc4 git submodule.
    $0 maude-cvc4-debug ...:     build_maude with debugging mode using the cvc4 git submodule.
    $0 maude-dreal4 ...:         build_maude using the dreal4 zip file.
" ;;
esac
