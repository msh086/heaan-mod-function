cmake_minimum_required(VERSION 3.22)
project(mod_heaan)

set(CMAKE_CXX_STANDARD 17)


add_executable(mod_heaan main.cpp)
target_include_directories(mod_heaan PRIVATE heaan/src)
target_link_libraries(mod_heaan pthread ntl gmp)
target_link_libraries(mod_heaan /home/msh/FHE/mod_heaan/heaan/lib/libHEAAN.a)