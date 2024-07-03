#!/usr/bin/env bash

# Settings/Utilities
# ------------------

# error if an variable is referenced before being set
set -u

# set variables
top_dir="$(pwd)"
src_dir="$(pwd)/src"

# maudesmc
smc_dir="maude-bindings/subprojects/maudesmc"

build_dir="$top_dir/$smc_dir/.build"
third_party="$top_dir/$smc_dir/.3rd_party"

# -------------------
include_dir="$build_dir/include"
lib_dir="$build_dir/lib"

# functionality
progress() { echo "===== " $@ ; }

build_deps() {
  build_gmp
  build_libsigsegv
  build_libncurses
  build_tecla
  build_libpoly
  build_buddy

  # build smt solver
  build_yices2

  rm -rf "$build_dir"/lib/*.so*
  rm -rf "$build_dir"/lib/*.dylib*
}

patch_src() {
  progress "Apply patchings"
  maude_src_dir="$top_dir/maude-bindings"
  patch_src_dir="$top_dir/src/patch"

  patch "$maude_src_dir/subprojects/maudesmc/src/Mixfix/commands.yy" < "$patch_src_dir/maude/mixfix-commands-yy.patch"
  patch "$maude_src_dir/subprojects/maudesmc/src/Mixfix/interpreter.hh" < "$patch_src_dir/maude/mixfix-interpreter-hh.patch"
  patch "$maude_src_dir/subprojects/maudesmc/src/Mixfix/lexer.ll" < "$patch_src_dir/maude/mixfix-lexer-ll.patch"
  patch "$maude_src_dir/subprojects/maudesmc/src/Mixfix/search.cc" < "$patch_src_dir/maude/mixfix-search-cc.patch"
  patch "$maude_src_dir/subprojects/maudesmc/src/Mixfix/top.yy" < "$patch_src_dir/maude/mixfix-top-yy.patch"
  patch "$maude_src_dir/subprojects/maudesmc/src/SMT/SMT.hh" < "$patch_src_dir/maude/smt-SMT-hh.patch"
  patch "$maude_src_dir/swig/maude.i" < "$patch_src_dir/swig/maude-i.patch"
  patch "$maude_src_dir/swig/term.i" < "$patch_src_dir/swig/term-i.patch"
  patch "$maude_src_dir/src/easyTerm.cc" < "$patch_src_dir/bindings/easyTerm-cc.patch"
  patch "$maude_src_dir/src/easyTerm.hh" < "$patch_src_dir/bindings/easyTerm-hh.patch"

  cp "$patch_src_dir/CMakeLists.txt" "$maude_src_dir"
  cp "$patch_src_dir/setup.py" "$maude_src_dir"
  cp "$patch_src_dir/meson_options.txt" "$maude_src_dir/subprojects/maudesmc/"
  cp "$patch_src_dir/meson.build" "$maude_src_dir/subprojects/maudesmc/"
}

prepare() {
  pip install scikit-build ninja cmake meson swig
  git clone https://github.com/fadoss/maude-bindings.git

  # currently use specific version
  cd maude-bindings && git checkout aefa8a8875dc3b82b6b0367cb73a1f533021d0e3
  git submodule update --init && rm -rf .git && rm -rf .github
}


build_src() {
  maude_src_dir="$top_dir/maude-bindings/subprojects/maudesmc/src"
  swig_src_dir="$top_dir/maude-bindings/swig"
  
  cp "$src_dir/core/smt_wrapper_interface.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/folder.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/folder.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSearchState.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSearchState.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSequenceSearch.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSequenceSearch.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/smtStateTransitionGraph.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/smtStateTransitionGraph.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSearch.cc" "$maude_src_dir/Mixfix"
  cp "$src_dir/swig/rwsmt.i" "$swig_src_dir"
  cp "$src_dir/swig/module.i" "$swig_src_dir"
  cp "$src_dir/swig/core.i"   "$swig_src_dir"
  cp "$src_dir/swig/python.i" "$swig_src_dir/specific"

  cd maude-bindings 
  (
    rm -rf dist/ maude.egg-info/ _skbuild/ dist/
    python setup.py bdist_wheel -DBUILD_LIBMAUDE=OFF
  )

  cd ..
  rm -rf ./out
  cp -r ./maude-bindings/dist ./out
}

build_maude_lib() {
  maude_src_dir="$top_dir/maude-bindings/subprojects/maudesmc/src"

  cp "$src_dir/core/smt_wrapper_interface.hh" "$maude_src_dir/SMT" 
  cp "$src_dir/maude/folder.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/folder.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSearchState.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSearchState.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSequenceSearch.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSequenceSearch.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/smtStateTransitionGraph.cc" "$maude_src_dir/SMT"
  cp "$src_dir/maude/smtStateTransitionGraph.hh" "$maude_src_dir/SMT"
  cp "$src_dir/maude/rewriteSmtSearch.cc" "$maude_src_dir/Mixfix"

  cd maude-bindings/subprojects/maudesmc
  (
    rm -rf release
    arch -arm64 meson setup release --buildtype=custom -Dcpp_args="-fno-stack-protector -fstrict-aliasing" \
          -Dextra-lib-dirs="$build_dir/lib" \
          -Dextra-include-dirs="$build_dir/include" \
          -Dstatic-libs='buddy, gmp, sigsegv, yices2' \
          -Dwith-smt='yices2' \
          -Dwith-ltsmin=disabled \
          -Dwith-simaude=disabled \
          -Dc_args='-mno-thumb' \
          -Dc_link_args="-Wl,--export-dynamic" \
          -Dcpp_link_args="-mmacosx-version-min=14.0 -Wl,-x -u ___gmpz_get_d -L"$build_dir"/lib -lgmp"
    cd release && ninja
  )
}

build_maude_se() {
  maudesmc_dir="$top_dir/maude-bindings/subprojects/maudesmc"
  swig_src_dir="$top_dir/maude-bindings/swig"

  mkdir -p $maudesmc_dir/build
  mkdir -p $maudesmc_dir/installdir/lib

  cp $maudesmc_dir/release/config.h $maudesmc_dir/build
  cp $maudesmc_dir/release/libmaude.dylib $maudesmc_dir/installdir/lib

  cp "$src_dir/swig/core.i"   "$swig_src_dir"
  cp "$src_dir/core/smt_wrapper.hh" "$top_dir/maude-bindings/src" 

  cd maude-bindings 
  (
    rm -rf dist/ maude.egg-info/ _skbuild/ dist/
    python setup.py bdist_wheel -DBUILD_LIBMAUDE=OFF \
          -DEXTRA_INCLUDE_DIRS="$maudesmc_dir/.build/include" \
          -DARCHFLAGS="-arch arm64"
  )

  cd ..
  rm -rf ./out
  cp -r ./maude-bindings/dist ./out
}

# build gmp
build_gmp() {
  progress "Building gmp library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading gmp 6.1.2"
    get_gnu "gmp" "6.1.2" "tar.xz"
    cd "$third_party/gmp-6.1.2"

    ./configure --prefix="$build_dir" CFLAGS=-fPIC CXXFLAGS=-fPIC \
		--enable-cxx --enable-fat --disable-shared --enable-static --build=x86_64-pc-linux-gnu
          
    make -j4
    make check
    make install
  )
}

build_yices2() {
  progress "Building Yices"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Yices2"
    git clone https://github.com/SRI-CSL/yices2 "$third_party/yices2"
    
    cd "$third_party/yices2"
    autoconf
    ./configure --prefix=$build_dir --with-static-gmp=$lib_dir/libgmp.a --with-static-gmp-include-dir=$include_dir \
                CFLAGS="-g -fno-stack-protector -O3" LDFLAGS="-L$lib_dir" CPPFLAGS="-I$include_dir"

    make -j4
    make install
  )

  rm -rf $build_dir/lib/libyices*.so*
  rm -rf $build_dir/lib/libyices*.dylib
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
    ./configure CFLAGS="-fPIC" CXXFLAGS="-fPIC" --includedir="$include_dir" --libdir="$lib_dir" --disable-shared
    
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

# build libncurses
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

# build libpoly for yices non linear support
build_libpoly() {
  progress "Building libpoly library"
  mkdir -p "$build_dir"
  mkdir -p "$third_party"
  ( progress "Downloading Libpoly"
    git clone https://github.com/SRI-CSL/libpoly.git "$third_party/libpoly"
    
    cd "$third_party/libpoly/build"
    cmake .. -DCMAKE_BUILD_TYPE="Release" -DCMAKE_INSTALL_PREFIX="$build_dir" -DGMP_LIBRARY="$lib_dir/libgmp.a" -DGMP_INCLUDE_DIR="$include_dir" -DCMAKE_C_FLAGS="-fPIC" -DCMAKE_CXX_FLAGS="-fPIC"
    make
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
    ./configure CFLAGS="-fPIC" CXXFLAGS="-fPIC" --prefix="$build_dir"

    make -j4 check
    make install
  )
}

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

# Follow the below steps
#  1. prepare
#  2. build_deps
#  3. patch_src
#  4. build_maude_lib
#  5. build_maude_se

# Main
# ----

build_command="$1" ; shift
case "$build_command" in
    prep)               prepare                   "$@" ;;
    deps)               build_deps                "$@" ;;
    patch)              patch_src                 "$@" ;;
    build-maude)        build_maude_lib           "$@" ;;
    build-maude-se)     build_maude_se            "$@" ;;
    *)      echo "
    usage: $0 [prep|deps|patch|build]
           $0 script <options>

    $0 prep     :   prepare Maude-as-a-library
    $0 deps     :   prepare Maude dependencies
    $0 patch    :   patch Maude-as-a-library
    $0 compile  :   compile Maude-SE
    $0 maude-se :   build Maude-SE
" ;;
esac