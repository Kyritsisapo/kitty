/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <algorithm>
#include <bitset>
#include <string>
#include <lpsolve/lp_lib.h>
#include "traits.hpp"
#include "algorithm.hpp"
#include "properties.hpp"
#include "print.hpp"
#include "cube.hpp"
#include "bit_operations.hpp"
#include "isop.hpp"
#include "dynamic_truth_table.hpp"
#include "static_truth_table.hpp"


namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/


template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{	
    TT ttable = tt;
    std::vector<bool> inv_var(ttable.num_vars(),false);
    std::vector<int64_t> linear_form;
    auto num_vars = ttable.num_vars();
    bool n, p;
	
	for (int i = 0; i< num_vars; i++){
		     
	  n=p=false;   
	  
	  for (auto bit = 0u; bit< (2 << (num_vars -1)); bit++){ //from monotone.properties
		  
		  if (get_bit( cofactor0(ttable, i), bit ) > get_bit( cofactor1(ttable, i), bit )){
			  
			  n = true;
		  }
		  if (get_bit( cofactor0(ttable, i), bit ) < get_bit( cofactor1(ttable, i), bit )){
			  
			  p = true;
		  }  
		  if (n && p){  // binate check
			  
			return false;
		  }			  
			  
	  }
	  if (n == true){
		  
		  inv_var.at(i) = true; //n_unate = true, there is a negative unate at i 
		   
		  flip_inplace(ttable, i); //flip variable i
		  
	  }
	} 
	
    const auto on_set =  isop(ttable);
    auto temp = unary_not(ttable);
    const auto off_set = isop(temp);


    /* lp_source code from lpsolve.sourceforge.net using version 5.5*/

    lprec *lp;
    int Ncol, *colno = NULL, ret = 0;  
    REAL *row = NULL;  
    
    int T_pos = num_vars + 1;
    Ncol = T_pos; // The number of columns is num_vars + 1 for T constraint (last)
    lp = make_lp(0, Ncol); 
    if(lp == NULL) 
		
        return false;       

    if(ret == 0) {

        colno = (int *) malloc(Ncol * sizeof(*colno));
        row = (REAL *) malloc(Ncol * sizeof(*row));
        if((colno == NULL) || (row == NULL))
			
            return false;
    }

    if(ret == 0) {
        set_add_rowmode(lp, TRUE);  
		
		for(int j = 0; j < Ncol; j++){
			
			auto k = 0;
            		colno[k] = j+1;
            		row[j] = ++k;
            
            add_constraintex(lp, k, row, colno, GE, 0);
            
        }
       		
        // using the on set cubes. First see if they exist, then add 1, otherwise 0
        for(int i = 0; i < on_set.size() ; i++){
			
            auto term = on_set.at(i);
            
            for(int j = 0; j < num_vars; j++){
				
                if(term.get_mask(j)){  
					       
                    colno[j] = j+1;
                    row[j] = 1;
                    
                }else{
					
		    colno[j] = j+1;                                        
                    row[j] = 0;
                   
                }
            }
            // ex : x1 + x2 >= T -> x1 + x2 - T >= 0
            colno[num_vars] = T_pos; //T constraint is on num+1
            row[num_vars] = -1;
            add_constraintex(lp, T_pos, row, colno, GE, 0);
        }
    }
    if(ret == 0) {
        
        for(int i = 0; i < off_set.size() ; i++){
			
            auto term = off_set.at(i);
            
            for(int j = 0; j < num_vars; j++){	
				
                if(term.get_mask(j)){  
					
		    colno[j] = j+1;                         
                    row[j] = 0;
                    
                }else{
					
		    colno[j] = j+1;                                             
                    row[j] = 1;
                   
                }

            }
            //ex: x1 + x2 <= T - 1 -> x1 + x2 - T <= -1
            colno[num_vars] = T_pos;
            row[num_vars] = -1;
            add_constraintex(lp, T_pos, row, colno, LE, -1);
        }
    }

    /*Add the objective function */
    if(ret == 0) {
        set_add_rowmode(lp, FALSE); /* rowmode should be turned off again when done building the model */
         
        for(int i = 0; i < Ncol; i++){
			
            colno[i] = i + 1;
            row[i] = 1;
        }
        
        if(!set_obj_fnex(lp, Ncol, row, colno))
			
		return false;
    }

    if(ret == 0) { //set for minimization (code from lpsolve.sourceforge)
        
        set_minim(lp);
        //write_LP( lp, stdout );
		set_verbose( lp, IMPORTANT);
        
        ret = solve(lp);
        if(ret == OPTIMAL)
            ret = 0;
		else 
			
		return false;
    }
    
    if(ret == 0) {	// fill the linear form 

        get_variables(lp, row);
        for(int j = 0; j < Ncol; j++){
            //printf("%s: %f\n", get_col_name(lp, j + 1), row[j]);
            linear_form.push_back(row[j]);
        }
        
    }
    // We inverted some variables due to neg. unate. We need to acquire the originals again
    for(int i = 0; i < num_vars; i++){
		
        if(inv_var.at(i)==true){
            
            linear_form.at(i) = -linear_form.at(i);
            linear_form.at(num_vars) = linear_form.at(num_vars) + linear_form.at(i); //rem. num vars is 1 more
        
        }
    }
   
    // free allocated memory (code from lpsolve.sourceforge)
    if(row != NULL)
    
        free(row);
        
    if(colno != NULL)
    
        free(colno);

    if(lp != NULL) {
       
        delete_lp(lp);
    }

	// finish!
    if ( plf )
    {
        *plf = linear_form;
    }
    return true;
}

}
