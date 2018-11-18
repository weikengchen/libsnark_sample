/**
 *****************************************************************************
 * @author     This file is part of libsnark, developed by SCIPR Lab
 *             and contributors (see AUTHORS).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#include <libff/algebra/curves/mnt/mnt4/mnt4_pp.hpp>
#include <libff/algebra/curves/mnt/mnt6/mnt6_pp.hpp>
#include <libff/algebra/fields/field_utils.hpp>

#include <libsnark/gadgetlib1/gadgets/fields/fp2_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/fields/fp3_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/fields/fp4_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/fields/fp6_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/verifiers/r1cs_ppzksnark_verifier_gadget.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/examples/r1cs_examples.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/gadgetlib1/gadgets/hashes/sha256/sha256_gadget.hpp>
#include <libsnark/gadgetlib1/gadgets/merkle_tree/merkle_tree_check_read_gadget.hpp>
//#include <assert.h>

#include <libsnark/gadgetlib1/examples/simple_example.hpp>

#include <iostream>

using namespace libsnark;
using namespace std;

template<typename FieldT>
void dump_constraints(const protoboard<FieldT> &pb)
{
#ifdef DEBUG
    for (auto s : pb.constraint_system.constraint_annotations)
    {
        printf("constraint: %s\n", s.second.c_str());
    }
#endif
}

template<typename ppT_A, typename ppT_B, typename FieldT, typename HashT>
protoboard< libff::Fr<ppT_B> > test_verifier_B(const r1cs_example<libff::Fr<ppT_A>> &example, const std::string &annotation_A, const std::string &annotation_B)
{
  typedef libff::Fr<ppT_A> FieldT_A;
  typedef libff::Fr<ppT_B> FieldT_B;

  assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
  const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(example.constraint_system);
  const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, example.primary_input, example.auxiliary_input);
  bool bit = r1cs_ppzksnark_verifier_strong_IC<ppT_A>(keypair.vk, example.primary_input, pi);
  assert(bit);

  const size_t elt_size = FieldT_A::size_in_bits();
  const size_t primary_input_size_in_bits = elt_size * example.constraint_system.primary_input_size;
  const size_t vk_size_in_bits = r1cs_ppzksnark_verification_key_variable<ppT_B>::size_in_bits(example.constraint_system.primary_input_size);

  protoboard<FieldT_B> pb;
  pb_variable_array<FieldT_B> vk_bits;
  vk_bits.allocate(pb, vk_size_in_bits, "vk_bits");

  pb_variable_array<FieldT_B> primary_input_bits;
  primary_input_bits.allocate(pb, primary_input_size_in_bits, "primary_input_bits");

  r1cs_ppzksnark_proof_variable<ppT_B> proof(pb, "proof");

  r1cs_ppzksnark_verification_key_variable<ppT_B> vk(pb, vk_bits, example.constraint_system.primary_input_size, "vk");

  pb_variable<FieldT_B> result;
  result.allocate(pb, "result");

  r1cs_ppzksnark_verifier_gadget<ppT_B> verifier(pb, vk, primary_input_bits, elt_size, proof, result, "verifier");

  PROFILE_CONSTRAINTS(pb, "check that proofs lies on the curve")
  {
      proof.generate_r1cs_constraints();
  }
  verifier.generate_r1cs_constraints();

  libff::bit_vector input_as_bits;
  for (const FieldT_A &el : example.primary_input)
  {
      libff::bit_vector v = libff::convert_field_element_to_bit_vector<FieldT_A>(el, elt_size);
      input_as_bits.insert(input_as_bits.end(), v.begin(), v.end());
  }

  primary_input_bits.fill_with_bits(pb, input_as_bits);

  vk.generate_r1cs_witness(keypair.vk);
  proof.generate_r1cs_witness(pi);
  verifier.generate_r1cs_witness();
  pb.val(result) = FieldT_B::one();

  printf("positive test:\n");
  assert(pb.is_satisfied());
  cerr<<pb.is_satisfied()<<endl;

  pb.val(primary_input_bits[0]) = FieldT_B::one() - pb.val(primary_input_bits[0]);
  verifier.generate_r1cs_witness();
  pb.val(result) = FieldT_B::one();

  printf("negative test:\n");
  assert(!pb.is_satisfied());
  cerr<<!pb.is_satisfied()<<endl;
  PRINT_CONSTRAINT_PROFILING();
  printf("number of constraints for verifier: %zu (verifier is implemented in %s constraints and verifies %s proofs))\n",
         pb.num_constraints(), annotation_B.c_str(), annotation_A.c_str());

  return pb;
}

template<typename ppT_A, typename ppT_B, typename FieldT, typename HashT>
void test_verifier(const std::string &annotation_A, const std::string &annotation_B)
{
  typedef libff::Fr<ppT_A> FieldT_A;
  typedef libff::Fr<ppT_B> FieldT_B;

  //const size_t num_constraints = 50;
  //const size_t primary_input_size = 1;

  //r1cs_example<FieldT_A> example = generate_r1cs_example_with_field_input<FieldT_A>(num_constraints, primary_input_size);
  //assert(example.primary_input.size() == primary_input_size);
  //r1cs_example<FieldT_A> example = gen_r1cs_example_from_protoboard<FieldT_A>(50);

  // generate the merkle tree instance
  const size_t digest_len = HashT::get_digest_len();
  const size_t tree_depth = 40;
  std::vector<merkle_authentication_node> path(tree_depth);

  libff::bit_vector prev_hash(digest_len);
  std::generate(prev_hash.begin(), prev_hash.end(), [&]() { return std::rand() % 2; });
  libff::bit_vector leaf = prev_hash;

  libff::bit_vector address_bits;

  size_t address = 0;
  for (long level = tree_depth-1; level >= 0; --level)
  {
      const bool computed_is_right = (std::rand() % 2);
      address |= (computed_is_right ? 1ul << (tree_depth-1-level) : 0);
      address_bits.push_back(computed_is_right);
      libff::bit_vector other(digest_len);
      std::generate(other.begin(), other.end(), [&]() { return std::rand() % 2; });

      libff::bit_vector block = prev_hash;
      block.insert(computed_is_right ? block.begin() : block.end(), other.begin(), other.end());
      libff::bit_vector h = HashT::get_hash(block);

      path[level] = other;

      prev_hash = h;
  }
  libff::bit_vector root = prev_hash;

  // generate protoboard for the merkle tree instance
  protoboard<FieldT> pb;

  pb_variable_array<FieldT> address_bits_va;

  address_bits_va.allocate(pb, tree_depth, "address_bits");
  digest_variable<FieldT> leaf_digest(pb, digest_len, "input_block");
  digest_variable<FieldT> root_digest(pb, digest_len, "output_digest");
  merkle_authentication_path_variable<FieldT, HashT> path_var(pb, tree_depth, "path_var");
  merkle_tree_check_read_gadget<FieldT, HashT> ml(pb, tree_depth, address_bits_va, leaf_digest, root_digest, path_var, ONE, "ml");

  pb.set_input_sizes(tree_depth+digest_len*2);

  path_var.generate_r1cs_constraints();
  ml.generate_r1cs_constraints();

  address_bits_va.fill_with_bits(pb, address_bits);
  assert(address_bits_va.get_field_element_from_bits(pb).as_ulong() == address);
  leaf_digest.generate_r1cs_witness(leaf);
  path_var.generate_r1cs_witness(address, path);
  root_digest.generate_r1cs_witness(root);
  ml.generate_r1cs_witness();


  address_bits_va.fill_with_bits(pb, address_bits);
  leaf_digest.generate_r1cs_witness(leaf);
  root_digest.generate_r1cs_witness(root);
  assert(pb.is_satisfied());
  cerr<<pb.is_satisfied()<<endl;
  cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

  r1cs_example<FieldT_A> new_example = r1cs_example<FieldT_A>(std::move(pb.get_constraint_system()), std::move(pb.primary_input()), std::move(pb.auxiliary_input()));

  const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(new_example.constraint_system);
  const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, new_example.primary_input, new_example.auxiliary_input);
  bool bit = r1cs_ppzksnark_verifier_strong_IC<ppT_A>(keypair.vk, new_example.primary_input, pi);
  assert(bit);
  cerr<<bit<<endl;

  // generate the verifier protoboard for the protoboard of the merkle tree instance
  //cerr<<new_example.constraint_system.auxiliary_input_size<<' '<<new_example.constraint_system.primary_input_size<<endl;
  //exit(0);
  cerr<<"\n\n\n\n===============\n\n\n\n"<<endl;


  test_verifier_B< ppT_A, ppT_B, FieldT, HashT>(new_example, annotation_A, annotation_B);

}

template<typename ppT_A, typename ppT_B>
void test_all_merkle_tree_gadgets()
{
    typedef libff::Fr<ppT_A> FieldT;

    test_verifier< ppT_A, ppT_B, FieldT, CRH_with_bit_out_gadget<FieldT> >("mnt4", "mnt6");
//    test_merkle_tree_check_read_gadget<FieldT, CRH_with_bit_out_gadget<FieldT> >();
//    test_merkle_tree_check_read_gadget<FieldT, sha256_two_to_one_hash_gadget<FieldT> >();

//    test_merkle_tree_check_update_gadget<FieldT, CRH_with_bit_out_gadget<FieldT> >();
//    test_merkle_tree_check_update_gadget<FieldT, sha256_two_to_one_hash_gadget<FieldT> >();
}

int main(void)
{
    libff::start_profiling();
    libff::mnt4_pp::init_public_params();
    libff::mnt6_pp::init_public_params();

    test_all_merkle_tree_gadgets<libff::mnt4_pp, libff::mnt6_pp>();
//    test_verifier<libff::mnt4_pp, libff::mnt6_pp>("mnt4", "mnt6");
//    test_verifier<libff::mnt6_pp, libff::mnt4_pp>("mnt6", "mnt4");

//    test_hardcoded_verifier<libff::mnt4_pp, libff::mnt6_pp>("mnt4", "mnt6");
//    test_hardcoded_verifier<libff::mnt6_pp, libff::mnt4_pp>("mnt6", "mnt4");
}
