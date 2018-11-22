/**
 *****************************************************************************
 * @author     This file is part of libsnark, developed by SCIPR Lab
 *             and contributors (see AUTHORS).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/

#include <libff/algebra/curves/mnt/mnt4/mnt4_pp.hpp>
#include <libff/algebra/curves/mnt/mnt6/mnt6_pp.hpp>
#include <libff/algebra/fields/field_utils.hpp>

/*#include <libsnark/gadgetlib1/gadgets/fields/fp2_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/fields/fp3_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/fields/fp4_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/fields/fp6_gadgets.hpp>*/

#include <libsnark/gadgetlib1/gadgets/verifiers/r1cs_ppzksnark_verifier_gadget.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/gadgetlib1/gadgets/merkle_tree/merkle_tree_check_update_gadget.hpp>

#include <iostream>
#include <fstream>
#include <sstream>

using namespace libsnark;
using namespace std;

template<typename ppT_A, typename FieldT_A, typename HashT> r1cs_ppzksnark_keypair<ppT_A> leaf_setup(const size_t tree_depth) {
    const size_t digest_len = HashT::get_digest_len();
    
    protoboard<FieldT_A> pb;
    
    // primary input
    digest_variable<FieldT_A> prev_root_digest(pb, digest_len, "prev_root_digest");
    digest_variable<FieldT_A> next_root_digest(pb, digest_len, "next_root_digest");
    
    // auxiliary input
    pb_variable_array<FieldT_A> address_bits_va;
    address_bits_va.allocate(pb, tree_depth, "address_bits");
    digest_variable<FieldT_A> prev_leaf_digest(pb, digest_len, "prev_leaf_digest");
    digest_variable<FieldT_A> next_leaf_digest(pb, digest_len, "next_leaf_digest");
    merkle_authentication_path_variable<FieldT_A, HashT> prev_path_var(pb, tree_depth, "prev_path_var");
    merkle_authentication_path_variable<FieldT_A, HashT> next_path_var(pb, tree_depth, "next_path_var");
    
    // load the Merkle tree gadget and generate the constraints
    merkle_tree_check_update_gadget<FieldT_A, HashT> mls(pb, tree_depth, address_bits_va,
                                                         prev_leaf_digest, prev_root_digest, prev_path_var,
                                                         next_leaf_digest, next_root_digest, next_path_var, pb_variable<FieldT_A>(0), "mls");
    prev_path_var.generate_r1cs_constraints();
    mls.generate_r1cs_constraints();
    
    const r1cs_constraint_system<FieldT_A> constraint_system = pb.get_constraint_system();
    cout << "Number of Leaf R1CS constraints: " << constraint_system.num_constraints() << endl;

    // generate a key pair
    const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(constraint_system);

    return keypair;
}


/*template<typename ppT_A, typename ppT_B> r1cs_example<libff::Fr<ppT_B> > test_verifier_B(const r1cs_example<libff::Fr<ppT_A> > &example, const std::string &annotation_A, const std::string &annotation_B, size_t &vk_size_in_Fields)
{
        typedef libff::Fr<ppT_A> FieldT_A;
        typedef libff::Fr<ppT_B> FieldT_B;

        assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
       
        const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, example.primary_input, example.auxiliary_input);

        const size_t elt_size = FieldT_A::size_in_bits();
        const size_t primary_input_size_in_bits = elt_size * example.constraint_system.primary_input_size;
        const size_t vk_size_in_bits = r1cs_ppzksnark_verification_key_variable<ppT_B>::size_in_bits(example.constraint_system.primary_input_size);
}*/

template<typename ppT_A, typename HashT_A>
void test_leaf_gen(const std::string &annotation)
{
    typedef libff::Fr<ppT_A> FieldT_A;

    // generate the key pair
    r1cs_ppzksnark_keypair<ppT_A> keypair = leaf_setup<ppT_A, FieldT_A, HashT_A>(16);
    
    // save the verifying key
    stringstream vk_leaf;
    vk_leaf << keypair.vk;
    
    ofstream fileOut;
    fileOut.open("vk_leaf");
    fileOut << vk_leaf.rdbuf();
    fileOut.close();
    
    // save the proving key
    stringstream pk_leaf;
    pk_leaf << keypair.pk;
    
    fileOut.open("pk_leaf");
    fileOut << pk_leaf.rdbuf();
    fileOut.close();
}


    
    /*

    // generate two Merkle tree paths.
    r1cs_example<FieldT_A> MT_1 = get_MT_instance<ppT_A, FieldT_A, HashT_A>(16);
    r1cs_example<FieldT_A> MT_2 = get_MT_instance<ppT_A, FieldT_A, HashT_A>(16);
    
    // generate the verifying key for MT
    assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
    
    
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
    */

int main(void)
{
    libff::start_profiling();
    libff::mnt4_pp::init_public_params();

	test_leaf_gen< libff::mnt4_pp, CRH_with_bit_out_gadget<libff::Fr<libff::mnt4_pp>> >("mnt4");
}
