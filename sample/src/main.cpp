/**
 *****************************************************************************
 * @author     This file is part of libsnark, developed by SCIPR Lab
 *             and contributors (see AUTHORS).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/

//#define DEBUG true

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

//#define DEBUG_LOCAL

/*
   template<typename FieldT>
   void dump_constraints(const protoboard<FieldT> &pb)
   {
   #ifdef DEBUG
        for (auto s : pb.constraint_system.constraint_annotations)
        {
                printf("constraint: %s\n", s.second.c_str());
        }
   #endif
   }*/
/*
   template<typename FieldT>
   void dump_r1cs_constraint(const r1cs_constraint<FieldT> &constraint,
                          const r1cs_variable_assignment<FieldT> &full_variable_assignment,
                          const std::map<size_t, std::string> &variable_annotations)
   {
        printf("terms for a:\n"); constraint.a.print_with_assignment(full_variable_assignment, variable_annotations);
        printf("terms for b:\n"); constraint.b.print_with_assignment(full_variable_assignment, variable_annotations);
        printf("terms for c:\n"); constraint.c.print_with_assignment(full_variable_assignment, variable_annotations);
   }
 */

template<typename FieldT_A, typename FieldT_B>
libff::bit_vector covert_input(const r1cs_primary_input<FieldT_A> &primary_input, const size_t elt_size)
{
        libff::bit_vector input_as_bits;
        for (const FieldT_A &el : primary_input)
        {
                libff::bit_vector v = libff::convert_field_element_to_bit_vector<FieldT_A>(el, elt_size);
                input_as_bits.insert(input_as_bits.end(), v.begin(), v.end());
        }
        return input_as_bits;
}

template<typename ppT_A, typename ppT_B>
protoboard< libff::Fr<ppT_B> > test_verifier_B(const r1cs_example<libff::Fr<ppT_A> > &example, const std::string &annotation_A, const std::string &annotation_B)
{
        typedef libff::Fr<ppT_A> FieldT_A;
        typedef libff::Fr<ppT_B> FieldT_B;

        assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
        const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(example.constraint_system);
        const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, example.primary_input, example.auxiliary_input);

#ifdef DEBUG_LOCAL
        bool bit = r1cs_ppzksnark_verifier_strong_IC<ppT_A>(keypair.vk, example.primary_input, pi);
        cerr<<bit<<endl;
        assert(bit);
#endif

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

        libff::bit_vector input_as_bits = covert_input<FieldT_A, FieldT_B>(example.primary_input, elt_size);

        primary_input_bits.fill_with_bits(pb, input_as_bits);

        vk.generate_r1cs_witness(keypair.vk);
        proof.generate_r1cs_witness(pi);
        verifier.generate_r1cs_witness();
        pb.val(result) = FieldT_B::one();

        pb.set_input_sizes(vk_size_in_bits + primary_input_size_in_bits);

        printf("positive test:\n");
        assert(pb.is_satisfied());
        cerr<<pb.is_satisfied()<<endl;
        cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

/*        pb.val(primary_input_bits[0]) = FieldT_B::one() - pb.val(primary_input_bits[0]);
        verifier.generate_r1cs_witness();
        pb.val(result) = FieldT_B::one();

        printf("negative test:\n");
        assert(!pb.is_satisfied());
        cerr<<!pb.is_satisfied()<<endl;*/

        PRINT_CONSTRAINT_PROFILING();
        printf("number of constraints for verifier: %zu (verifier is implemented in %s constraints and verifies %s proofs))\n",
               pb.num_constraints(), annotation_B.c_str(), annotation_A.c_str());

        return pb;
}

template<typename ppT_A, typename FieldT_A, typename HashT>
r1cs_example<FieldT_A> get_MT_instance(const size_t tree_depth)
{
        // generate the merkle tree instance
        const size_t digest_len = HashT::get_digest_len();
        //const size_t tree_depth = 16;
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
        protoboard<FieldT_A> pb;

        pb_variable_array<FieldT_A> address_bits_va;

        address_bits_va.allocate(pb, tree_depth, "address_bits");
        digest_variable<FieldT_A> leaf_digest(pb, digest_len, "input_block");
        digest_variable<FieldT_A> root_digest(pb, digest_len, "output_digest");
        merkle_authentication_path_variable<FieldT_A, HashT> path_var(pb, tree_depth, "path_var");
        merkle_tree_check_read_gadget<FieldT_A, HashT> ml(pb, tree_depth, address_bits_va, leaf_digest, root_digest, path_var, pb_variable<FieldT_A>(0), "ml");

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

#ifdef DEBUG_LOCAL
        const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(new_example.constraint_system);
        const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, new_example.primary_input, new_example.auxiliary_input);
        bool bit = r1cs_ppzksnark_verifier_strong_IC<ppT_A>(keypair.vk, new_example.primary_input, pi);
        assert(bit);
        cerr<<bit<<endl;
#endif

        return new_example;
}

template<typename ppT_A, typename ppT_B, typename FieldT_A, typename FieldT_B>
void add_offset(linear_combination<FieldT_B> &a, const size_t offset_0, const size_t offset_1, const size_t boardline)
{
        for (size_t c=0; c< a.terms.size(); ++c)
        {
                // [0] always represents 0 and is not included in primary_input
                if (a.terms[c].index == 0) {
                        continue;
                }
                if (a.terms[c].index <= boardline)
                {
                        a.terms[c].index += offset_0;
                } else {
                        a.terms[c].index += offset_1;
                }
        }
}

template<typename ppT_A, typename ppT_B, typename FieldT_A, typename FieldT_B>
r1cs_constraint_system<FieldT_B> add_offset_to_index(const protoboard<FieldT_B> &pb, const size_t offset_0, const size_t offset_1)
{
        r1cs_constraint_system<FieldT_B> cs = move(pb.get_constraint_system());
        for (size_t c = 0; c < cs.constraints.size(); ++c)
        {
                add_offset<ppT_A, ppT_B, FieldT_A, FieldT_B>(cs.constraints[c].a, offset_0, offset_1, cs.primary_input_size);
                add_offset<ppT_A, ppT_B, FieldT_A, FieldT_B>(cs.constraints[c].b, offset_0, offset_1, cs.primary_input_size);
                add_offset<ppT_A, ppT_B, FieldT_A, FieldT_B>(cs.constraints[c].c, offset_0, offset_1, cs.primary_input_size);
        }
        return cs;
}

template<typename ppT_A, typename ppT_B, typename FieldT_A, typename FieldT_B>
r1cs_example<FieldT_B> merge_proof(const protoboard<FieldT_B> &pb_1, const protoboard<FieldT_B> &pb_2)
{
        size_t offset_0 = 0;
        size_t offset_1 = pb_2.primary_input().size();
        size_t offset_2 = pb_1.primary_input().size();
        size_t offset_3 = pb_1.primary_input().size() + pb_1.auxiliary_input().size();
/*
        protoboard<FieldT_A> pb;
        pb_variable_array<FieldT_A> primary_input_bits;
        primary_input_bits.allocate(pb, pb_1.primary_input().size() + pb_2.primary_input().size(), "primary_input");

        pb_variable_array<FieldT_A> auxiliary_input_bits;
        auxiliary_input_bits.allocate(pb, pb_1.auxiliary_input().size() + pb_2.auxiliary_input().size(), "auxiliary_input");
 */
        r1cs_constraint_system<FieldT_B> cs_1 = add_offset_to_index<ppT_A, ppT_B, FieldT_A, FieldT_B>(pb_1, offset_0, offset_1);
        r1cs_constraint_system<FieldT_B> cs_2 = add_offset_to_index<ppT_A, ppT_B, FieldT_A, FieldT_B>(pb_2, offset_2, offset_3);

        r1cs_constraint_system<FieldT_B> cs;
        cs.constraints.insert(cs.constraints.end(), cs_1.constraints.begin(), cs_1.constraints.end());
        cs.constraints.insert(cs.constraints.end(), cs_2.constraints.begin(), cs_2.constraints.end());

        cs.primary_input_size = pb_1.primary_input().size() + pb_2.primary_input().size();
        cs.auxiliary_input_size = pb_1.auxiliary_input().size() + pb_2.auxiliary_input().size();

        r1cs_primary_input<FieldT_B> primary_input_1(pb_1.primary_input());
        r1cs_primary_input<FieldT_B> primary_input_2(pb_2.primary_input());
        r1cs_primary_input<FieldT_B> auxiliary_input_1(pb_1.auxiliary_input());
        r1cs_primary_input<FieldT_B> auxiliary_input_2(pb_2.auxiliary_input());

        r1cs_primary_input<FieldT_B> new_primary_input;
        new_primary_input.insert(new_primary_input.end(), primary_input_1.begin(), primary_input_1.end());
        new_primary_input.insert(new_primary_input.end(), primary_input_2.begin(), primary_input_2.end());

        r1cs_primary_input<FieldT_B> new_auxiliary_input;
        new_auxiliary_input.insert(new_auxiliary_input.end(), auxiliary_input_1.begin(), auxiliary_input_1.end());
        new_auxiliary_input.insert(new_auxiliary_input.end(), auxiliary_input_2.begin(), auxiliary_input_2.end());

/*
        r1cs_variable_assignment<FieldT_B> full_variable_assignment = new_primary_input;
        full_variable_assignment.insert(full_variable_assignment.end(), new_auxiliary_input.begin(), new_auxiliary_input.end());
        dump_r1cs_constraint<FieldT_B>(cs.constraints[0], full_variable_assignment, cs.variable_annotations);
 */
        r1cs_example<FieldT_B> example = r1cs_example<FieldT_B>(move(cs), move(new_primary_input), move(new_auxiliary_input));
        return example;
}

template<typename ppT_A, typename ppT_B, typename HashT_A, typename HashT_B>
void test_verifier(const std::string &annotation_A, const std::string &annotation_B)
{
        typedef libff::Fr<ppT_A> FieldT_A;
        typedef libff::Fr<ppT_B> FieldT_B;

        // generate the verifier protoboard for the protoboard of the merkle tree instance
        r1cs_example<FieldT_A> new_example = get_MT_instance<ppT_A, FieldT_A, HashT_A>(2);
        protoboard<FieldT_B> pb_1 = test_verifier_B< ppT_A, ppT_B >(new_example, annotation_A, annotation_B);

        // try recursive proofs
        cerr<<"start second proof"<<endl;
        r1cs_example<FieldT_A> another_example = get_MT_instance<ppT_A, FieldT_A, HashT_A>(2);
        protoboard<FieldT_B> pb_2 = test_verifier_B< ppT_A, ppT_B >(another_example, annotation_A, annotation_B);

        r1cs_example<FieldT_B> cs(pb_1.get_constraint_system(), pb_2.primary_input(), pb_2.auxiliary_input());
        cerr<<cs.constraint_system.is_satisfied(cs.primary_input, cs.auxiliary_input)<<endl;
        //exit(0);

        // merge proof
        r1cs_example<FieldT_B> final_example = merge_proof< ppT_A, ppT_B, FieldT_A, FieldT_B>(pb_1, pb_2);

        cerr<<"test final proof"<<endl;
        assert(final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input));
        cerr<<final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input)<<endl;

        cerr<<final_example.primary_input.size()<<' '<<final_example.auxiliary_input.size()<<endl;
        cerr<<final_example.constraint_system.num_constraints()<<endl;
        const r1cs_ppzksnark_keypair<ppT_B> keypair = r1cs_ppzksnark_generator<ppT_B>(final_example.constraint_system);
        const r1cs_ppzksnark_proof<ppT_B> pi = r1cs_ppzksnark_prover<ppT_B>(keypair.pk, final_example.primary_input, final_example.auxiliary_input);
        bool bit = r1cs_ppzksnark_verifier_strong_IC<ppT_B>(keypair.vk, final_example.primary_input, pi);
        assert(bit);
        cerr<<bit<<endl;
}

template<typename ppT_A, typename ppT_B>
void test_all_merkle_tree_gadgets()
{
        typedef libff::Fr<ppT_A> FieldT_A;
        typedef libff::Fr<ppT_B> FieldT_B;

        test_verifier< ppT_A, ppT_B, CRH_with_bit_out_gadget<FieldT_A>,  CRH_with_bit_out_gadget<FieldT_B> >("mnt4", "mnt6");
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
