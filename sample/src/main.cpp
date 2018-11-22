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
#include <libsnark/gadgetlib1/gadgets/merkle_tree/merkle_tree_check_update_gadget.hpp>

#include <iostream>

using namespace libsnark;
using namespace std;

template<typename ppT_A, typename FieldT_A, typename HashT> r1cs_example<FieldT_A> get_MT_instance(const size_t tree_depth);

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

template<typename ppT_A, typename ppT_B> r1cs_example<libff::Fr<ppT_B> > test_verifier_B(const r1cs_example<libff::Fr<ppT_A> > &example, const std::string &annotation_A, const std::string &annotation_B, size_t &vk_size_in_Fields)
{
        typedef libff::Fr<ppT_A> FieldT_A;
        typedef libff::Fr<ppT_B> FieldT_B;

        assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
       
        const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, example.primary_input, example.auxiliary_input);

        const size_t elt_size = FieldT_A::size_in_bits();
        const size_t primary_input_size_in_bits = elt_size * example.constraint_system.primary_input_size;
        const size_t vk_size_in_bits = r1cs_ppzksnark_verification_key_variable<ppT_B>::size_in_bits(example.constraint_system.primary_input_size);

        protoboard<FieldT_B> pb;

	cerr<<"input size"<<endl;

        pb_variable_array<FieldT_B> vk_bits;
        vk_bits.allocate(pb, vk_size_in_bits, "vk_bits");
	cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

        pb_variable_array<FieldT_B> primary_input_bits;
        primary_input_bits.allocate(pb, primary_input_size_in_bits, "primary_input_bits");
	cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

        r1cs_ppzksnark_proof_variable<ppT_B> proof(pb, "proof");
	cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

        r1cs_ppzksnark_verification_key_variable<ppT_B> vk(pb, vk_bits, example.constraint_system.primary_input_size, "vk");
	cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

        pb_variable<FieldT_B> result;
        result.allocate(pb, "result");
	cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

        r1cs_ppzksnark_verifier_gadget<ppT_B> verifier(pb, vk, primary_input_bits, elt_size, proof, result, "verifier");
	cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

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

        cerr<<"divide: "<<vk_size_in_bits % elt_size <<endl;
        pb.set_input_sizes(vk_size_in_bits / elt_size + example.constraint_system.primary_input_size);
        vk_size_in_Fields = vk_size_in_bits / elt_size;

        //cerr<<pb.num_inputs()<<' '<<vk_size_in_bits / elt_size + example.constraint_system.primary_input_size<<endl;

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

        return r1cs_example<FieldT_B>(pb.get_constraint_system(), pb.primary_input(), pb.auxiliary_input());
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
r1cs_constraint_system<FieldT_B> add_offset_to_index(const r1cs_example<FieldT_B> &pb, const size_t offset_0, const size_t offset_1)
{
        r1cs_constraint_system<FieldT_B> cs = move(pb.constraint_system);
        for (size_t c = 0; c < cs.constraints.size(); ++c)
        {
                add_offset<ppT_A, ppT_B, FieldT_A, FieldT_B>(cs.constraints[c].a, offset_0, offset_1, cs.primary_input_size);
                add_offset<ppT_A, ppT_B, FieldT_A, FieldT_B>(cs.constraints[c].b, offset_0, offset_1, cs.primary_input_size);
                add_offset<ppT_A, ppT_B, FieldT_A, FieldT_B>(cs.constraints[c].c, offset_0, offset_1, cs.primary_input_size);
        }
        return cs;
}

template<typename ppT_A, typename ppT_B, typename FieldT_A, typename FieldT_B>
r1cs_example<FieldT_B> merge_verifier(const r1cs_example<FieldT_B> &pb_1, const r1cs_example<FieldT_B> &pb_2)
{
        cerr<<"start merge_verifier"<<endl;
        size_t offset_0 = 0;
        size_t offset_1 = pb_2.primary_input.size();
        size_t offset_2 = pb_1.primary_input.size();
        size_t offset_3 = pb_1.primary_input.size() + pb_1.auxiliary_input.size();
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

        cs.primary_input_size = pb_1.primary_input.size() + pb_2.primary_input.size();
        cs.auxiliary_input_size = pb_1.auxiliary_input.size() + pb_2.auxiliary_input.size();

        r1cs_primary_input<FieldT_B> primary_input_1(pb_1.primary_input);
        r1cs_primary_input<FieldT_B> primary_input_2(pb_2.primary_input);
        r1cs_primary_input<FieldT_B> auxiliary_input_1(pb_1.auxiliary_input);
        r1cs_primary_input<FieldT_B> auxiliary_input_2(pb_2.auxiliary_input);

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

template<typename FieldT_B>
void merge_index(linear_combination<FieldT_B> &a, const size_t l1, const size_t r1, const size_t l2, const size_t r2)
{
        for (size_t c=0; c< a.terms.size(); ++c)
        {
                // [0] always represents 0 and is not included in primary_input
                if (a.terms[c].index < l2) {
                        continue;
                }
                else if (a.terms[c].index <= r2) {
                        a.terms[c].index = l1 + (a.terms[c].index - l2);
                }
                else {
                        a.terms[c].index -= (r2-l2+1);
                }
        }
}

template<typename FieldT_B>
void merge_inputs(r1cs_example<FieldT_B> &ex, size_t l1, size_t r1, size_t l2, size_t r2)
{
        for (size_t c = 0; c < ex.constraint_system.constraints.size(); ++c)
        {
                merge_index<FieldT_B>(ex.constraint_system.constraints[c].a, l1, r1, l2, r2);
                merge_index<FieldT_B>(ex.constraint_system.constraints[c].b, l1, r1, l2, r2);
                merge_index<FieldT_B>(ex.constraint_system.constraints[c].c, l1, r1, l2, r2);
        }
        r1cs_primary_input<FieldT_B> tmp(ex.primary_input);
        ex.primary_input.clear();
        ex.primary_input.insert(ex.primary_input.end(), tmp.begin(), tmp.begin()+l2);
        ex.primary_input.insert(ex.primary_input.end(), tmp.begin()+r2+1, tmp.end());
}

template<typename ppT_A, typename ppT_B, typename HashT_A>
void test_verifier(const std::string &annotation_A, const std::string &annotation_B)
{
    typedef libff::Fr<ppT_A> FieldT_A;
    typedef libff::Fr<ppT_B> FieldT_B;

    size_t vk_size_in_Fields;
    
    //

    // generate two Merkle tree paths.
    r1cs_example<FieldT_A> MT_1 = get_MT_instance<ppT_A, FieldT_A, HashT_A>(16);
    r1cs_example<FieldT_A> MT_2 = get_MT_instance<ppT_A, FieldT_A, HashT_A>(16);
    
    // generate the verifying key for MT
    assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
    const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(example.constraint_system);
    
    	// generate the verifier protoboard for the protoboard of the merkle tree instance

    
    r1cs_example<FieldT_B> verifier_1 = test_verifier_B< ppT_A, ppT_B >(new_example, annotation_A, annotation_B, vk_size_in_Fields);

        // try recursive proofs
        cerr<<"start second proof"<<endl;
        
        r1cs_example<FieldT_B> verifier_2 = test_verifier_B< ppT_A, ppT_B >(another_example, annotation_A, annotation_B, vk_size_in_Fields);
        verifier_2.constraint_system = verifier_1.constraint_system;
        //protoboard<FieldT_B> pb_2(pb_1.get_constraint_system, another_example.primary_input, another_example.auxiliary_input);


        //r1cs_example<FieldT_B> cs(pb_1.get_constraint_system(), pb_2.primary_input(), pb_2.auxiliary_input());
        //cerr<<cs.constraint_system.is_satisfied(cs.primary_input, cs.auxiliary_input)<<endl;
        //exit(0);

        // merge proof
        r1cs_example<FieldT_B> final_example = merge_verifier< ppT_A, ppT_B, FieldT_A, FieldT_B>(verifier_1, verifier_2);

        cerr<<"test final proof"<<endl;
        assert(final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input));
        cerr<<final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input)<<endl;

        size_t primary_input_size_1 = verifier_1.primary_input.size();
        size_t digest_len = HashT_B::get_digest_len();
        cerr<<HashT_A::get_digest_len() << ' '<<HashT_B::get_digest_len()<<endl;
        assert(HashT_A::get_digest_len() ==  HashT_B::get_digest_len());
        merge_inputs<FieldT_B>(final_example, vk_size_in_Fields + 1 + digest_len*2, vk_size_in_Fields + 1 + digest_len*4, primary_input_size_1 + vk_size_in_Fields + 1, primary_input_size_1 + vk_size_in_Fields + 1 + digest_len*2);
        merge_inputs<FieldT_B>(final_example, 0, vk_size_in_Fields-1, primary_input_size_1, primary_input_size_1 + vk_size_in_Fields - 1);

        cerr<<final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input)<<endl;
}

int main(void)
{
    libff::start_profiling();
    libff::mnt4_pp::init_public_params();
    libff::mnt6_pp::init_public_params();

	test_verifier< libff::mnt4_pp, libff::mnt6_pp, CRH_with_bit_out_gadget<libff::Fr<libff::mnt4_pp>> >("mnt4", "mnt6");
}

template<typename ppT_A, typename FieldT_A, typename HashT> r1cs_example<FieldT_A> get_MT_instance(const size_t tree_depth) {
        // generate the merkle tree instance
        const size_t digest_len = HashT::get_digest_len();
    
        std::vector<merkle_authentication_node> prev_path(tree_depth);

        libff::bit_vector prev_load_hash(digest_len);
        std::generate(prev_load_hash.begin(), prev_load_hash.end(), [&]() { return std::rand() % 2; });
        libff::bit_vector prev_store_hash(digest_len);
        std::generate(prev_store_hash.begin(), prev_store_hash.end(), [&]() { return std::rand() % 2; });

        libff::bit_vector loaded_leaf = prev_load_hash;
        libff::bit_vector stored_leaf = prev_store_hash;

        libff::bit_vector address_bits;

        size_t address = 0;
        for (long level = tree_depth-1; level >= 0; --level)
        {
                const bool computed_is_right = (std::rand() % 2);
                address |= (computed_is_right ? 1ul << (tree_depth-1-level) : 0);
                address_bits.push_back(computed_is_right);
                libff::bit_vector other(digest_len);
                std::generate(other.begin(), other.end(), [&]() { return std::rand() % 2; });

                libff::bit_vector load_block = prev_load_hash;
                load_block.insert(computed_is_right ? load_block.begin() : load_block.end(), other.begin(), other.end());
                libff::bit_vector store_block = prev_store_hash;
                store_block.insert(computed_is_right ? store_block.begin() : store_block.end(), other.begin(), other.end());

                libff::bit_vector load_h = HashT::get_hash(load_block);
                libff::bit_vector store_h = HashT::get_hash(store_block);

                prev_path[level] = other;

                prev_load_hash = load_h;
                prev_store_hash = store_h;
        }

        libff::bit_vector load_root = prev_load_hash;
        libff::bit_vector store_root = prev_store_hash;

        /* execute the test */
        protoboard<FieldT_A> pb;
        pb_variable_array<FieldT_A> address_bits_va;
        address_bits_va.allocate(pb, tree_depth, "address_bits");
        digest_variable<FieldT_A> prev_leaf_digest(pb, digest_len, "prev_leaf_digest");
        digest_variable<FieldT_A> prev_root_digest(pb, digest_len, "prev_root_digest");
        digest_variable<FieldT_A> next_leaf_digest(pb, digest_len, "next_leaf_digest");
        digest_variable<FieldT_A> next_root_digest(pb, digest_len, "next_root_digest");
    
        merkle_authentication_path_variable<FieldT_A, HashT> prev_path_var(pb, tree_depth, "prev_path_var");
        merkle_authentication_path_variable<FieldT_A, HashT> next_path_var(pb, tree_depth, "next_path_var");
    
        merkle_tree_check_update_gadget<FieldT_A, HashT> mls(pb, tree_depth, address_bits_va,
                                                             prev_leaf_digest, prev_root_digest, prev_path_var,
                                                             next_leaf_digest, next_root_digest, next_path_var, pb_variable<FieldT_A>(0), "mls");

        prev_path_var.generate_r1cs_constraints();
        mls.generate_r1cs_constraints();

        address_bits_va.fill_with_bits(pb, address_bits);
        assert(address_bits_va.get_field_element_from_bits(pb).as_ulong() == address);
        prev_leaf_digest.generate_r1cs_witness(loaded_leaf);
        prev_path_var.generate_r1cs_witness(address, prev_path);
        next_leaf_digest.generate_r1cs_witness(stored_leaf);
        address_bits_va.fill_with_bits(pb, address_bits);
        mls.generate_r1cs_witness();

        /* make sure that update check will check for the right things */
        prev_leaf_digest.generate_r1cs_witness(loaded_leaf);
        next_leaf_digest.generate_r1cs_witness(stored_leaf);
        prev_root_digest.generate_r1cs_witness(load_root);
        next_root_digest.generate_r1cs_witness(store_root);
        address_bits_va.fill_with_bits(pb, address_bits);
        assert(pb.is_satisfied());

        pb.set_input_sizes(1+digest_len*4);

        const size_t num_constraints = pb.num_constraints();
        const size_t expected_constraints = merkle_tree_check_update_gadget<FieldT_A, HashT>::expected_constraints(tree_depth);
        assert(num_constraints == expected_constraints);
        cerr<<pb.is_satisfied()<<endl;
        cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;

        r1cs_example<FieldT_A> new_example = r1cs_example<FieldT_A>(std::move(pb.get_constraint_system()), std::move(pb.primary_input()), std::move(pb.auxiliary_input()));

        return new_example;
}
