include_directories(.)

add_executable(
  main-leaf

  main-leaf.cpp
)
add_executable(
  main-leaf-unpacked

  main-leaf-unpacked.cpp
)
add_executable(
  main-layer2

  main-layer2.cpp
)
target_link_libraries(
  main-leaf

  snark
)
target_link_libraries(
  main-leaf-unpacked

  snark
)
target_link_libraries(
  main-layer2

  snark
)
target_include_directories(
  main-leaf

  PUBLIC
  ${DEPENDS_DIR}/libsnark
  ${DEPENDS_DIR}/libsnark/depends/libfqfft
)
target_include_directories(
  main-leaf-unpacked

  PUBLIC
  ${DEPENDS_DIR}/libsnark
  ${DEPENDS_DIR}/libsnark/depends/libfqfft
)
target_include_directories(
  main-layer2

  PUBLIC
  ${DEPENDS_DIR}/libsnark
  ${DEPENDS_DIR}/libsnark/depends/libfqfft
)
