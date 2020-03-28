install cmake and ninja by running,
sudo apt install cmake ninja-build
git clone https://github.com/piyus/CSE601.git
cd CSE601
mkdir build
cd build
cp ../scripts/build.sh .
sh build.sh
ninja
** it will take a while **
** after the build completes **
cd ../tests
make

This is my implementation of CSE601 (compiler design) course project "SafeC".
The goal of safeC is to ensure "temporal", "type" and "spatial" safety for a subset of C programs. All implementation is done at LLVM IR level. We also catch "null pointer dereferences" by dynamic checks and dataflow analysis on LLVM IR. 
