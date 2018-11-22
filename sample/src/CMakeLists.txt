include_directories(.)

add_executable(
  main-leaf

  main-leaf.cpp
)
target_link_libraries(
  main-leaf

  snark
)
target_include_directories(
  main-leaf

  PUBLIC
  ${DEPENDS_DIR}/libsnark
  ${DEPENDS_DIR}/libsnark/depends/libfqfft
)
