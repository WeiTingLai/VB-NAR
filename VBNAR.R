
######################################
#  Variational Bayes for VAR model   #
#    2020/03/01                      #   
######################################



#============= VAR-Variatonal Bayesian function ============================
VB_NAR<-function(Y,X=NULL,segment,lag,maxit=1e+5,tol=1e-8,phi_initial,alpha_initial,mu_initial,sigma_initial, sigma_beta_initial,verbose=T,cv=F)
{
  #===========Use Package ==============
  require (mvtnorm)
  require(gtools)
  require(boot)
  require(psych)
  library(MASS)
  library(Matrix)
  library(MCMCpack)
  #============ Functon =====================
  other_part<-function(j,s, item)
  {
    if(length(segment)==1)
    {
      item_new<-item[,(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))]
    }else{
      item_new<-item[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][,-c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]
      if(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))>=sum(segment[c(1:s)]))
      {
        item_new<-cbind(item_new[,c(0:(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-sum((segment_eachrow[[j]])[s])-1))],item[,(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))],item_new[,unlist(ifelse(sum(c(0:(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-sum((segment_eachrow[[j]])[s])-1)))==0,list(c((ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-sum((segment_eachrow[[j]])[s])):ncol(item_new))),list(-c(0:(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-sum((segment_eachrow[[j]])[s])-1)))))])
      }else{
        if(s==1){
          item_new<-cbind(item[,(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))],item_new)
        }else{
          if(rep(1:length(segment),c(segment))[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]==s){
            item_new<-cbind(item_new[,c(0:sum(segment[c(1:(s-1))]))],item[,(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))],item_new[,unlist(ifelse(sum(c(0:sum(segment[c(1:(s-1))])))==0,list(c((sum(segment[c(1:(s-1))])+1):ncol(item_new))),list(-c(0:sum(segment[c(1:(s-1))])))))])
          }else{
            item_new<-cbind(item_new[,c(0:(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-1))],item[,(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))],item_new[,unlist(ifelse(sum(c(0:(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-1)))==0,list(c(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)):ncol(item_new))),list(-c(0:(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))-1)))))])
            
          }
        }
      }
    }
    return( matrix(item_new,nrow=nrow(item)))
  } #except sth segment
  #==================model setting==================================   
  m<-ncol(Y)
  p<-lag
  n<-nrow(Y)
  criteria<-T
  group<-c(0,rep(c(1,(m-1)),p*m))
  segment_eachrow<-matrix(t(as.list(lapply(1:(p*m),function(j)table(rep(1:length(segment),c(segment))[ifelse(j%%m!=0,-(j%%m),-m)])))),ncol=1)
   if(verbose){
    message("Info: Segment :",length(segment))
    message("Info: Sample of size:",ifelse(is.null(X),n,n))
    message("Info: Number of Lags:",p)
  }
  
  #================ Data setting =============================
  Y<-as.matrix(Y)
  if(is.null(X)){
    X1<-rep(0,p*m)
    for(j in 2:p)
    {
      
      X1<-rbind(X1,c(c(t(Y[c((j-1):1),])),rep(0,p*m-length(c(t(Y[c((j-1):1),]))))) )
    }
    X<-t(sapply((p+1):nrow(Y),function(j)c(t(Y[c((j-1):(j-p)),]))))
    X<-rbind(X1,X)
    
  }
  X<-as.matrix(X)
  
  if(missing(mu_initial)) {mu_initial<-ginv(crossprod(X, X))%*%crossprod(X,Y)}
  if(missing(alpha_initial)) {alpha_initial=c(0.01,0.01) }
  if(missing(sigma_initial)){sigma_initial<-var(Y)/2}
  if(missing(sigma_beta_initial)) {sigma_beta_initial<-sigma_initial}
  if(missing(phi_initial)){phi_initial<-matrix(c(rep(0,p*(m^2))),ncol=m) }
  if(length(mu_initial)==1){mu_iitial<-rep(mu_initial,m^2*p)}
  if(length(alpha_initial)==1){alpha_initial<-rep(alpha_initial,2)}
  if(length(sigma_initial)==1){sigma_initial<-diag(sigma_initial,m)}
  if(length(sigma_beta_initial)==1){sigma_beta_initial<-diag(sigma_beta_initial,m)}
  if(length(phi_initial)==1){phi_initial<-matrix(c(rep(1,p*(m^2))),ncol=m)}
  if(length(mu_initial)!=m^2*p | length(alpha_initial)!=2 |length(sigma_initial)!=m^2 |length(sigma_beta_initial)!=m^2|length(phi_initial)!=p*(m^2)){
    stop("initial parameter settings are not consisitent")
  }
  
  ELBO <- rep(-1e+15, maxit+1)
  mu_element_diag<-rep(0,ncol(X))
  mu_element_segment<-matrix(0,nrow=ncol(X),ncol=(ncol(Y)-1))
  phi_coef<-rep(0,(length(group)-1))
  
    beta_mean<-matrix(sapply(1:ncol(X),function(j)phi_initial[j,]*mu_initial[j,]),ncol=ncol(Y),byrow=T)
    sigma_inv<-ginv(sigma_initial)
    sigma_beta_element_diag<-diag(chol2inv(chol(diag(diag(sigma_inv),ncol(X))*diag(diag(crossprod(X,X)),ncol(X))+diag(1/diag(sigma_beta_initial),ncol(X)))))
    sigma_beta_element_segment<-lapply(1:nrow(mu_initial),function(j)sapply(1:length(segment_eachrow[[j]]),function(s)ifelse(j%%ncol(Y)!=0,list(chol2inv(chol(as.numeric(crossprod(X[,j],X[,j]))*(sigma_inv[-(j%%ncol(Y)),][,-(j%%ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]+chol2inv(chol((sigma_beta_initial[-(j%%ncol(Y)),][,-(j%%ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]))))),list(chol2inv(chol(as.numeric(crossprod(X[,j],X[,j]))*(sigma_inv[-(ncol(Y)),][,-(ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]+chol2inv(chol((sigma_beta_initial[-(ncol(Y)),][,-(ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]))))))))
    
    for(j in 1:ncol(X))
    { 
      
      mu_element_diag[j]<-((sigma_beta_element_diag)[j]%*%((sigma_inv[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)),  ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])%*%(crossprod(X[,j],(Y[,ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]-X[,-(j)]%*%beta_mean[-(j),ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])))+tr(matrix(sigma_inv[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)),  -ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))],nrow=1)%*%matrix(crossprod(X[,j],(Y[,-ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]-X%*%beta_mean[,-ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])),nrow=m-1))))
      phi_coef[2*j-1]<-list(inv.logit(ifelse(j%%ncol(Y)!=0,log(alpha_initial[1]/(1-alpha_initial[1]+1e-15))-(1/2)*log(diag(sigma_beta_initial)[j%%ncol(Y)])+(1/2)*log(det(diag(sigma_beta_element_diag[j],1)))+(mu_element_diag[j]^2)/(2*sigma_beta_element_diag[j]) ,log(alpha_initial[1]/(1-alpha_initial[1]+1e-15))-(1/2)*log(diag(sigma_beta_initial)[ncol(Y)])+(1/2)*log(det(diag(sigma_beta_element_diag[j],1)))+(mu_element_diag[j]^2)/(2*sigma_beta_element_diag[j]) )))
      beta_mean[j,ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]<-unlist(phi_coef[[2*j-1]])*mu_element_diag[j]
      
      mu_element_segment[j,]<-unlist(sapply(1:length(segment_eachrow[[j]]),function(s)(crossprod(X[,j],((Y[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))])[,c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]-X[,-(j)]%*%beta_mean[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][-(j),][,c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]))%*%(sigma_inv[-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))),][,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))])%*%(matrix(unlist((sigma_beta_element_segment)[[j]][[s]]),ncol=segment_eachrow[[j]][[s]])))+(crossprod(X[,j],((other_part(j,s,Y)-X%*%other_part(j,s,beta_mean)))%*%(t((matrix(matrix(other_part(j,s,sigma_inv)[-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))),],nrow=m-1)[c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)])),],nrow=segment_eachrow[[j]][[s]])))))%*%matrix(unlist((sigma_beta_element_segment)[[j]][[s]]),ncol=segment_eachrow[[j]][[s]]))))
      
      phi_coef[2*j]<-list(inv.logit(sapply(1:length(segment_eachrow[[j]]),function(s)ifelse(j%%ncol(Y)!=0,log(alpha_initial[2]/(1-alpha_initial[2]+1e-15))-(1/2)*log(det(matrix(sigma_beta_initial[-(j%%ncol(Y)),][,-(j%%ncol(Y))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=segment_eachrow[[j]][[s]])))+(1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))]%*%chol2inv(chol(sigma_beta_element_segment[[(j)]][[s]]))%*%matrix(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=1)/2),log(alpha_initial[2]/(1-alpha_initial[2]))-(1/2)*log(det(matrix(sigma_beta_initial[-(ncol(Y)),][,-(ncol(Y))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=segment_eachrow[[j]][[s]])))+(1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))]%*%chol2inv(chol(sigma_beta_element_segment[[(j)]][[s]]))%*%matrix(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=1)/2) ))))
      beta_mean[j,ifelse(j%%ncol(Y)!=0,-(j%%ncol(Y)),-(ncol(Y)))]<- unlist(rep(unlist(phi_coef[[2*j]]),segment_eachrow[[j]]))*mu_element_segment[j,]
      
      
    }
    phi_real<-matrix(unlist(sapply(1:(p*m),function(j){A<-cbind(phi_coef[[2*j-1]],matrix(rep(phi_coef[[2*j]],segment_eachrow[[j]]),nrow=1));ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(A),{A[,c(1:(j%%ncol(Y)))]<-c(A[,c(2:(j%%ncol(Y)))],A[,1]);list(A)}),{A[,c(1:(ncol(Y)))]<-c(A[,c(2:(ncol(Y)))],A[,1]);list(A)})})),ncol=ncol(Y),byrow=T)
    mu_element<-cbind(mu_element_diag,mu_element_segment)
    mu_element<-matrix(unlist(sapply(1:ncol(X),function(j)ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(mu_element[j,]),{mu_element[j,c(1:(j%%ncol(Y)))]<-c(mu_element[j,c(2:(j%%ncol(Y)))],mu_element[j,1]);list(mu_element[j,])}),{mu_element[j,c(1:(ncol(Y)))]<-c(mu_element[j,c(2:(ncol(Y)))],mu_element[j,1]);list(mu_element[j,])}))),ncol=ncol(Y),byrow=T)
    
    
    beta_var<-sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))))
    ;C<-as.numeric(crossprod(X[,j],X[,j]))*superMatrix(A,B);ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,{C[c(1:(j%%ncol(Y))),]<-C[c((j%%ncol(Y)):1),];C[,c(1:(j%%ncol(Y)))]<-C[,c((j%%ncol(Y)):1)];list(C)},{C[c(1:(j%%ncol(Y))),]<-C[c(c(2:(j%%ncol(Y))),1),];C[,c(1:(j%%ncol(Y)))]<-C[,c(c(2:(j%%ncol(Y))),1)];list(C)}),{C[c(1:(ncol(Y))),]<-C[c((2:(ncol(Y))),1),];C[,c(1:(ncol(Y)))]<-C[,c((2:(ncol(Y))),1)];list(C)})})
    
    sigma_hat<-(1/nrow(Y))*(crossprod(Y,Y)-crossprod(Y,(X%*%beta_mean))-crossprod((X%*%beta_mean),Y)+matrix(apply(sapply(1:ncol(X),function(j)c(unlist(beta_var[j]))),1,sum),ncol(Y)) +matrix(apply(sapply(1:ncol(X),function(j)as.numeric(crossprod(X[,j],X[,j]))*crossprod(matrix(beta_mean[j,],ncol=ncol(Y)),matrix(beta_mean[j,],ncol=ncol(Y)))),1,sum),ncol=ncol(Y))
                            +matrix(apply(sapply(1:ncol(X),function(j)crossprod(matrix(matrix(X[,j],ncol=1)%*%beta_mean[j,],ncol=ncol(Y)),matrix((X[,-j]%*%beta_mean[-j,]),ncol=ncol(Y)))),1,sum),ncol(Y))
    )
    sigma_beta<-sum(sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))));sum(A+phi_coef[[2*j-1]]*mu_element_diag[j]^2+tr(matrix(unlist(B),ncol=m-1))+(rep(phi_coef[[2*j]],segment_eachrow[[j]])*mu_element_segment[j,])%*%t(matrix(mu_element_segment[j,],ncol=(ncol(Y)-1))))}))/(sum(sapply(1:ncol(X),function(j)phi_coef[[2*j-1]]))+sum(unlist(sapply(1:ncol(X),function(j)segment_eachrow[[j]]*phi_coef[[2*j]]))))
    alpha<-apply(matrix(sapply(1:ncol(X),function(j)c(sum(phi_coef[[2*j-1]]),sum(phi_coef[[2*j]]))),ncol=2,byrow=T),2,sum)/c(ncol(X),length(segment)*ncol(X))
    ln_y <-  -((nrow(Y)*ncol(Y))/2)*log(2*pi)-(nrow(Y)/2)*det(matrix(sigma_hat,ncol=m))-tr(chol2inv(chol(matrix(sigma_hat,ncol=m)))*(nrow(Y)/2)*matrix(sigma_hat,ncol=m))+1e-500
    
    ln_r <-  sum(sapply(1:ncol(X),function(j) phi_coef[[2*j-1]]*log(alpha[1]+1e-15/(phi_coef[[2*j-1]]+1e-15))+(1- phi_coef[[2*j-1]])*log((1-alpha[1]+1e-15)/(1-phi_coef[[2*j-1]]+1e-15))))
    
    ln_eta <- sum(unlist(sapply(1:ncol(X),function(j) phi_coef[[2*j]]*log(alpha[2]+1e-15/(phi_coef[[2*j]]+1e-15))+ (1-phi_coef[[2*j]])*log((1-alpha[2]+1e-15)/(1-phi_coef[[2*j]]+1e-15)))))
    
    ln_coef_segment <- sum(unlist(sapply(1:ncol(X),function(j) sapply(1:length(segment_eachrow[[j]]),function(s)phi_coef[[2*j]][s]*((1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(1/2)*tr(chol2inv(chol(sigma_beta_element_segment[[j]][[s]]))%*%sigma_beta_element_segment[[j]][[s]])-(segment_eachrow[[j]][[s]]/2)*log(sigma_beta)-(1/2)*tr(chol2inv(chol(diag(sigma_beta,segment_eachrow[[j]][[s]])))%*%(sigma_beta_element_segment[[j]][[s]]+crossprod(matrix(mu_element_segment[j,unlist(ifelse(s==1,{list(c(1:segment_eachrow[[j]][[s]]))},{list(c((sum(segment_eachrow[[j]][c(1:(s-1))])+1):sum(segment_eachrow[[j]][c(1:s)])))}))],nrow=1),matrix(mu_element_segment[j,unlist(ifelse(s==1,{list(c(1:segment_eachrow[[j]][[s]]))},{list(c((sum(segment_eachrow[[j]][c(1:(s-1))])+1):sum(segment_eachrow[[j]][c(1:s)])))}))],nrow=1)))))))))
    
    ln_coef_diag<- sum(sapply(1:ncol(X),function(j) phi_coef[[2*j-1]]*((1/2)*log(sigma_beta_element_diag[[j]])+(1/2)*(sigma_beta_element_diag[[j]])/sigma_beta_element_diag[[j]]-(1/2)*log(sigma_beta)-(1/2)*(sigma_beta_element_diag[[j]]+mu_element_diag[j]^2)/sigma_beta)))
    
    ELBO[2] <- ln_y + ln_r + ln_eta + ln_coef_segment + ln_coef_diag
    test<- -1e+5
    
    for( itera in 2:maxit)
    {
      
      criteria<-(abs(ELBO[itera]-ELBO[itera-1])>tol) *( abs(test-mean((Y-X%*%beta_mean)^2))>tol)
      
      
      if(criteria){cat("Iteration:", itera-1,"th","\tELBO:",ELBO[itera],"\tELBO_diff:", abs(ELBO[itera] - ELBO[itera-1]),"\ttest:", test,"\n")}else{iteration<-itera;break}
      test<-mean((Y-X%*%beta_mean)^2)
      
      sigma_beta_segment<-diag(sigma_beta,(ncol(Y)))
      sigma_inv<-chol2inv(chol(matrix(sigma_hat,ncol=ncol(Y))))
      sigma_beta_element_diag<-diag(chol2inv(chol(diag(diag(sigma_inv),ncol(X))*diag(diag(crossprod(X,X)),ncol(X))+diag(1/sigma_beta,ncol(X)))))
      sigma_beta_element_segment<-lapply(1:nrow(mu_initial),function(j)sapply(1:length(segment_eachrow[[j]]),function(s)ifelse(j%%ncol(Y)!=0,list(chol2inv(chol(as.numeric(crossprod(X[,j],X[,j]))*(sigma_inv[-(j%%ncol(Y)),][,-(j%%ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]+chol2inv(chol((sigma_beta_segment[-(j%%ncol(Y)),][,-(j%%ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]))))),list(chol2inv(chol(as.numeric(crossprod(X[,j],X[,j]))*(sigma_inv[-(ncol(Y)),][,-(ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]+chol2inv(chol((sigma_beta_segment[-(ncol(Y)),][,-(ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]))))))))
      
      for(j in 1:(p*m))
      { 
        
        mu_element_diag[j]<-((sigma_beta_element_diag)[j]%*%((sigma_inv[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)),  ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])%*%(crossprod(X[,j],(Y[,ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]-X[,-(j)]%*%beta_mean[-(j),ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])))+tr(matrix(sigma_inv[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)),  -ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))],nrow=1)%*%matrix(crossprod(X[,j],(Y[,-ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]-X%*%beta_mean[,-ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])),nrow=m-1))))
        phi_coef[2*j-1]<-list(inv.logit(ifelse(j%%ncol(Y)!=0,log(alpha[1]/(1-alpha[1]+1e-15))-(1/2)*log(sigma_beta)+(1/2)*log(det(diag(sigma_beta_element_diag[j],1)))+(mu_element_diag[j]^2)/(2*sigma_beta_element_diag[j]) ,log(alpha[1]/(1-alpha[1]+1e-15))-(1/2)*log(sigma_beta)+(1/2)*log(det(diag(sigma_beta_element_diag[j],1)))+(mu_element_diag[j]^2)/(2*sigma_beta_element_diag[j]) )))
        beta_mean[j,ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]<-unlist(phi_coef[[2*j-1]])*mu_element_diag[j]
        
        mu_element_segment[j,]<-unlist(sapply(1:length(segment_eachrow[[j]]),function(s)(crossprod(X[,j],((Y[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))])[,c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]-X[,-(j)]%*%beta_mean[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][-(j),][,c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]))%*%(sigma_inv[-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))),][,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))])%*%(matrix(unlist((sigma_beta_element_segment)[[j]][[s]]),ncol=segment_eachrow[[j]][[s]])))+(crossprod(X[,j],((other_part(j,s,Y)-X%*%other_part(j,s,beta_mean)))%*%(t((matrix(matrix(other_part(j,s,sigma_inv)[-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))),],nrow=m-1)[c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)])),],nrow=segment_eachrow[[j]][[s]])))))%*%matrix(unlist((sigma_beta_element_segment)[[j]][[s]]),ncol=segment_eachrow[[j]][[s]]))))
        
        phi_coef[2*j]<-list(inv.logit(sapply(1:length(segment_eachrow[[j]]),function(s)ifelse(j%%ncol(Y)!=0,log(alpha[2]/(1-alpha[2]+1e-15))-(1/2)*log(det(matrix(sigma_beta_segment[-(j%%ncol(Y)),][,-(j%%ncol(Y))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=segment_eachrow[[j]][[s]])))+(1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))]%*%chol2inv(chol(sigma_beta_element_segment[[(j)]][[s]]))%*%matrix(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=1)/2),log(alpha[2]/(1-alpha[2]+1e-15))-(1/2)*log(det(matrix(sigma_beta_segment[-(ncol(Y)),][,-(ncol(Y))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=segment_eachrow[[j]][[s]])))+(1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))]%*%chol2inv(chol(sigma_beta_element_segment[[(j)]][[s]]))%*%matrix(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=1)/2) ))))
        
        beta_mean[j,ifelse(j%%ncol(Y)!=0,-(j%%ncol(Y)),-(ncol(Y)))]<- unlist(rep(unlist(phi_coef[[2*j]]),segment_eachrow[[j]]))*mu_element_segment[j,]
        
        
      }
      phi_real<-matrix(unlist(sapply(1:(p*m),function(j){A<-cbind(phi_coef[[2*j-1]],matrix(rep(phi_coef[[2*j]],segment_eachrow[[j]]),nrow=1));ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(A),{A[,c(1:(j%%ncol(Y)))]<-c(A[,c(2:(j%%ncol(Y)))],A[,1]);list(A)}),{A[,c(1:(ncol(Y)))]<-c(A[,c(2:(ncol(Y)))],A[,1]);list(A)})})),ncol=ncol(Y),byrow=T)
      mu_element<-cbind(mu_element_diag,mu_element_segment)
      mu_element<-matrix(unlist(sapply(1:ncol(X),function(j)ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(mu_element[j,]),{mu_element[j,c(1:(j%%ncol(Y)))]<-c(mu_element[j,c(2:(j%%ncol(Y)))],mu_element[j,1]);list(mu_element[j,])}),{mu_element[j,c(1:(ncol(Y)))]<-c(mu_element[j,c(2:(ncol(Y)))],mu_element[j,1]);list(mu_element[j,])}))),ncol=ncol(Y),byrow=T)
      
      
      beta_var<-sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))))
      ;C<-as.numeric(crossprod(X[,j],X[,j]))*superMatrix(A,B);ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,{C[c(1:(j%%ncol(Y))),]<-C[c((j%%ncol(Y)):1),];C[,c(1:(j%%ncol(Y)))]<-C[,c((j%%ncol(Y)):1)];list(C)},{C[c(1:(j%%ncol(Y))),]<-C[c(c(2:(j%%ncol(Y))),1),];C[,c(1:(j%%ncol(Y)))]<-C[,c(c(2:(j%%ncol(Y))),1)];list(C)}),{C[c(1:(ncol(Y))),]<-C[c((2:(ncol(Y))),1),];C[,c(1:(ncol(Y)))]<-C[,c((2:(ncol(Y))),1)];list(C)})})
      
      sigma_hat<-(1/nrow(Y))*(crossprod(Y,Y)-crossprod(Y,(X%*%beta_mean))-crossprod((X%*%beta_mean),Y)+matrix(apply(sapply(1:ncol(X),function(j)c(unlist(beta_var[j]))),1,sum),ncol(Y)) +matrix(apply(sapply(1:ncol(X),function(j)as.numeric(crossprod(X[,j],X[,j]))*crossprod(matrix(beta_mean[j,],ncol=ncol(Y)),matrix(beta_mean[j,],ncol=ncol(Y)))),1,sum),ncol=ncol(Y))
                              +matrix(apply(sapply(1:ncol(X),function(j)crossprod(matrix(matrix(X[,j],ncol=1)%*%beta_mean[j,],ncol=ncol(Y)),matrix((X[,-j]%*%beta_mean[-j,]),ncol=ncol(Y)))),1,sum),ncol(Y))
      )
      sigma_beta<-sum(sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))));sum(A+phi_coef[[2*j-1]]*mu_element_diag[j]^2+tr(matrix(unlist(B),ncol=m-1))+(rep(phi_coef[[2*j]],segment_eachrow[[j]])*mu_element_segment[j,])%*%t(matrix(mu_element_segment[j,],ncol=(ncol(Y)-1))))}))/(sum(sapply(1:ncol(X),function(j)phi_coef[[2*j-1]]))+sum(unlist(sapply(1:ncol(X),function(j)segment_eachrow[[j]]*phi_coef[[2*j]]))))
      alpha<-apply(matrix(sapply(1:ncol(X),function(j)c(sum(phi_coef[[2*j-1]]),sum(phi_coef[[2*j]]))),ncol=2,byrow=T),2,sum)/c(ncol(X),length(segment)*ncol(X))
      ln_y <-  -((nrow(Y)*ncol(Y))/2)*log(2*pi)-(nrow(Y)/2)*det(matrix(sigma_hat,ncol=m))-tr(chol2inv(chol(matrix(sigma_hat,ncol=m)))*(nrow(Y)/2)*matrix(sigma_hat,ncol=m))
      
      ln_r <-  sum(sapply(1:ncol(X),function(j) phi_coef[[2*j-1]]*log(alpha[1]+1e-15/(phi_coef[[2*j-1]]+1e-15))+(1- phi_coef[[2*j-1]])*log((1-alpha[1]+1e-15)/(1-phi_coef[[2*j-1]]+1e-15))))
      
      ln_eta <- sum(unlist(sapply(1:ncol(X),function(j) phi_coef[[2*j]]*log(alpha[2]+1e-15/(phi_coef[[2*j]]+1e-15))+ (1-phi_coef[[2*j]])*log((1-alpha[2]+1e-15)/(1-phi_coef[[2*j]]+1e-15)))))
      
      ln_coef_segment <- sum(unlist(sapply(1:ncol(X),function(j) sapply(1:length(segment_eachrow[[j]]),function(s)phi_coef[[2*j]][s]*((1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(1/2)*tr(chol2inv(chol(sigma_beta_element_segment[[j]][[s]]))%*%sigma_beta_element_segment[[j]][[s]])-(segment_eachrow[[j]][[s]]/2)*log(sigma_beta)-(1/2)*tr(chol2inv(chol(diag(sigma_beta,segment_eachrow[[j]][[s]])))%*%(sigma_beta_element_segment[[j]][[s]]+crossprod(matrix(mu_element_segment[j,unlist(ifelse(s==1,{list(c(1:segment_eachrow[[j]][[s]]))},{list(c((sum(segment_eachrow[[j]][c(1:(s-1))])+1):sum(segment_eachrow[[j]][c(1:s)])))}))],nrow=1),matrix(mu_element_segment[j,unlist(ifelse(s==1,{list(c(1:segment_eachrow[[j]][[s]]))},{list(c((sum(segment_eachrow[[j]][c(1:(s-1))])+1):sum(segment_eachrow[[j]][c(1:s)])))}))],nrow=1)))))))))
      
      ln_coef_diag<- sum(sapply(1:ncol(X),function(j) phi_coef[[2*j-1]]*((1/2)*log(sigma_beta_element_diag[[j]])+(1/2)*(sigma_beta_element_diag[[j]])/sigma_beta_element_diag[[j]]-(1/2)*log(sigma_beta)-(1/2)*(sigma_beta_element_diag[[j]]+mu_element_diag[j]^2)/sigma_beta)))
      
      
      ELBO[itera+1] <- ln_y + ln_r + ln_eta + ln_coef_segment + ln_coef_diag
    }
    phi1<-lapply(1:(length(group)-1),function(j){phi_coef[[j]][which(phi_coef[[j]]>=.5)]<-phi_coef[[j]][which(phi_coef[[j]]>=.5)];phi_coef[[j]][which(phi_coef[[j]]<.5)]<-0;phi_coef[[j]]})
    phi<- unlist(phi1)
    phi_real<-matrix(unlist(sapply(1:(p*m),function(j){A<-cbind(phi1[[2*j-1]],matrix(rep(phi1[[2*j]],segment_eachrow[[j]]),nrow=1));ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(A),{A[,c(1:(j%%ncol(Y)))]<-c(A[,c(2:(j%%ncol(Y)))],A[,1]);list(A)}),{A[,c(1:(ncol(Y)))]<-c(A[,c(2:(ncol(Y)))],A[,1]);list(A)})})),ncol=ncol(Y),byrow=T)
    
    
    beta_mean<-matrix(sapply(1:ncol(X),function(j)phi_real[j,]*mu_element[j,]),ncol=ncol(Y),byrow=T)
    phi_coef<-phi1
    beta_var<-sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))))
    ;C<-as.numeric(crossprod(X[,j],X[,j]))*superMatrix(A,B);ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,{C[c(1:(j%%ncol(Y))),]<-C[c((j%%ncol(Y)):1),];C[,c(1:(j%%ncol(Y)))]<-C[,c((j%%ncol(Y)):1)];list(C)},{C[c(1:(j%%ncol(Y))),]<-C[c(c(2:(j%%ncol(Y))),1),];C[,c(1:(j%%ncol(Y)))]<-C[,c(c(2:(j%%ncol(Y))),1)];list(C)}),{C[c(1:(ncol(Y))),]<-C[c((2:(ncol(Y))),1),];C[,c(1:(ncol(Y)))]<-C[,c((2:(ncol(Y))),1)];list(C)})})
    
    sigma_hat<-(1/nrow(Y))*(crossprod(Y,Y)-crossprod(Y,(X%*%beta_mean))-crossprod((X%*%beta_mean),Y)+matrix(apply(sapply(1:ncol(X),function(j)c(unlist(beta_var[j]))),1,sum),ncol(Y)) +matrix(apply(sapply(1:ncol(X),function(j)as.numeric(crossprod(X[,j],X[,j]))*crossprod(matrix(beta_mean[j,],ncol=ncol(Y)),matrix(beta_mean[j,],ncol=ncol(Y)))),1,sum),ncol=ncol(Y))
                            +matrix(apply(sapply(1:ncol(X),function(j)crossprod(matrix(matrix(X[,j],ncol=1)%*%beta_mean[j,],ncol=ncol(Y)),matrix((X[,-j]%*%beta_mean[-j,]),ncol=ncol(Y)))),1,sum),ncol(Y))
    )
    sigma_beta<-sum(sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))));sum(A+phi_coef[[2*j-1]]*mu_element_diag[j]^2+tr(matrix(unlist(B),ncol=m-1))+(rep(phi_coef[[2*j]],segment_eachrow[[j]])*mu_element_segment[j,])%*%t(matrix(mu_element_segment[j,],ncol=(ncol(Y)-1))))}))/(sum(sapply(1:ncol(X),function(j)phi_coef[[2*j-1]]))+sum(unlist(sapply(1:ncol(X),function(j)segment_eachrow[[j]]*phi_coef[[2*j]]))))
    alpha<-apply(matrix(sapply(1:ncol(X),function(j)c(sum(phi_coef[[2*j-1]]),sum(phi_coef[[2*j]]))),ncol=2,byrow=T),2,sum)/c(ncol(X),length(segment)*ncol(X))
    
  
  for( itera in itera:maxit)
  {
    phi_coef_pre<-phi1
    mu_element_pre<-mu_element
    
    sigma_beta_segment<-diag(sigma_beta,(ncol(Y)))
    sigma_inv<-chol2inv(chol(matrix(sigma_hat,ncol=ncol(Y))))
    sigma_beta_element_diag<-diag(chol2inv(chol(diag(diag(sigma_inv),ncol(X))*diag(diag(crossprod(X,X)),ncol(X))+diag(1/sigma_beta,ncol(X)))))
    sigma_beta_element_segment<-lapply(1:nrow(mu_initial),function(j)sapply(1:length(segment_eachrow[[j]]),function(s)ifelse(j%%ncol(Y)!=0,list(chol2inv(chol(as.numeric(crossprod(X[,j],X[,j]))*(sigma_inv[-(j%%ncol(Y)),][,-(j%%ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]+chol2inv(chol((sigma_beta_segment[-(j%%ncol(Y)),][,-(j%%ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]))))),list(chol2inv(chol(as.numeric(crossprod(X[,j],X[,j]))*(sigma_inv[-(ncol(Y)),][,-(ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]+chol2inv(chol((sigma_beta_segment[-(ncol(Y)),][,-(ncol(Y))])[c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][s]+1):sum(segment_eachrow[[j]][c(1:s)]))]))))))))
    
    for(j in 1:(p*m))
    { 
      
      mu_element_diag[j]<-((sigma_beta_element_diag)[j]%*%((sigma_inv[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)),  ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])%*%(crossprod(X[,j],(Y[,ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]-X[,-(j)]%*%beta_mean[-(j),ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])))+tr(matrix(sigma_inv[ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)),  -ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))],nrow=1)%*%matrix(crossprod(X[,j],(Y[,-ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]-X%*%beta_mean[,-ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))])),nrow=m-1))))
      phi_coef[2*j-1]<-list(inv.logit(ifelse(j%%ncol(Y)!=0,log(alpha[1]/(1-alpha[1]+1e-15))-(1/2)*log(sigma_beta)+(1/2)*log(det(diag(sigma_beta_element_diag[j],1)))+(mu_element_diag[j]^2)/(2*sigma_beta_element_diag[j]) ,log(alpha[1]/(1-alpha[1]+1e-15))-(1/2)*log(sigma_beta)+(1/2)*log(det(diag(sigma_beta_element_diag[j],1)))+(mu_element_diag[j]^2)/(2*sigma_beta_element_diag[j]) )))
      beta_mean[j,ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))]<-unlist(phi_coef[[2*j-1]])*mu_element_diag[j]
      
      mu_element_segment[j,]<-unlist(sapply(1:length(segment_eachrow[[j]]),function(s)(crossprod(X[,j],((Y[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))])[,c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]-X[,-(j)]%*%beta_mean[,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][-(j),][,c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))]))%*%(sigma_inv[-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))),][,-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y)))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)]))])%*%(matrix(unlist((sigma_beta_element_segment)[[j]][[s]]),ncol=segment_eachrow[[j]][[s]])))+(crossprod(X[,j],((other_part(j,s,Y)-X%*%other_part(j,s,beta_mean)))%*%(t((matrix(matrix(other_part(j,s,sigma_inv)[-(ifelse(j%%ncol(Y)!=0,j%%ncol(Y),ncol(Y))),],nrow=m-1)[c((sum(segment_eachrow[[j]][c(1:s)])-(segment_eachrow[[j]][[s]])+1):sum(segment_eachrow[[j]][c(1:s)])),],nrow=segment_eachrow[[j]][[s]])))))%*%matrix(unlist((sigma_beta_element_segment)[[j]][[s]]),ncol=segment_eachrow[[j]][[s]]))))
      
      phi_coef[2*j]<-list(inv.logit(sapply(1:length(segment_eachrow[[j]]),function(s)ifelse(j%%ncol(Y)!=0,log(alpha[2]/(1-alpha[2]+1e-15))-(1/2)*log(det(matrix(sigma_beta_segment[-(j%%ncol(Y)),][,-(j%%ncol(Y))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=segment_eachrow[[j]][[s]])))+(1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))]%*%chol2inv(chol(sigma_beta_element_segment[[(j)]][[s]]))%*%matrix(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=1)/2),log(alpha[2]/(1-alpha[2]+1e-15))-(1/2)*log(det(matrix(sigma_beta_segment[-(ncol(Y)),][,-(ncol(Y))][c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)])),c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=segment_eachrow[[j]][[s]])))+(1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))]%*%chol2inv(chol(sigma_beta_element_segment[[(j)]][[s]]))%*%matrix(mu_element_segment[j,c((sum(segment_eachrow[[j]][c(1:s)])-segment_eachrow[[j]][[s]]+1):sum(segment_eachrow[[j]][c(1:s)]))],ncol=1)/2) ))))
      
      beta_mean[j,ifelse(j%%ncol(Y)!=0,-(j%%ncol(Y)),-(ncol(Y)))]<- unlist(rep(unlist(phi_coef[[2*j]]),segment_eachrow[[j]]))*mu_element_segment[j,]
      
      
    }
    phi_real<-matrix(unlist(sapply(1:(p*m),function(j){A<-cbind(phi_coef[[2*j-1]],matrix(rep(phi_coef[[2*j]],segment_eachrow[[j]]),nrow=1));ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(A),{A[,c(1:(j%%ncol(Y)))]<-c(A[,c(2:(j%%ncol(Y)))],A[,1]);list(A)}),{A[,c(1:(ncol(Y)))]<-c(A[,c(2:(ncol(Y)))],A[,1]);list(A)})})),ncol=ncol(Y),byrow=T)
    mu_element<-cbind(mu_element_diag,mu_element_segment)
    mu_element<-matrix(unlist(sapply(1:ncol(X),function(j)ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(mu_element[j,]),{mu_element[j,c(1:(j%%ncol(Y)))]<-c(mu_element[j,c(2:(j%%ncol(Y)))],mu_element[j,1]);list(mu_element[j,])}),{mu_element[j,c(1:(ncol(Y)))]<-c(mu_element[j,c(2:(ncol(Y)))],mu_element[j,1]);list(mu_element[j,])}))),ncol=ncol(Y),byrow=T)
    
    
    beta_var<-sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))))
    ;C<-as.numeric(crossprod(X[,j],X[,j]))*superMatrix(A,B);ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,{C[c(1:(j%%ncol(Y))),]<-C[c((j%%ncol(Y)):1),];C[,c(1:(j%%ncol(Y)))]<-C[,c((j%%ncol(Y)):1)];list(C)},{C[c(1:(j%%ncol(Y))),]<-C[c(c(2:(j%%ncol(Y))),1),];C[,c(1:(j%%ncol(Y)))]<-C[,c(c(2:(j%%ncol(Y))),1)];list(C)}),{C[c(1:(ncol(Y))),]<-C[c((2:(ncol(Y))),1),];C[,c(1:(ncol(Y)))]<-C[,c((2:(ncol(Y))),1)];list(C)})})
    
    sigma_hat<-(1/nrow(Y))*(crossprod(Y,Y)-crossprod(Y,(X%*%beta_mean))-crossprod((X%*%beta_mean),Y)+matrix(apply(sapply(1:ncol(X),function(j)c(unlist(beta_var[j]))),1,sum),ncol(Y)) +matrix(apply(sapply(1:ncol(X),function(j)as.numeric(crossprod(X[,j],X[,j]))*crossprod(matrix(beta_mean[j,],ncol=ncol(Y)),matrix(beta_mean[j,],ncol=ncol(Y)))),1,sum),ncol=ncol(Y))
                            +matrix(apply(sapply(1:ncol(X),function(j)crossprod(matrix(matrix(X[,j],ncol=1)%*%beta_mean[j,],ncol=ncol(Y)),matrix((X[,-j]%*%beta_mean[-j,]),ncol=ncol(Y)))),1,sum),ncol(Y))
    )
    sigma_beta<-sum(sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))));sum(A+phi_coef[[2*j-1]]*mu_element_diag[j]^2+tr(matrix(unlist(B),ncol=m-1))+(rep(phi_coef[[2*j]],segment_eachrow[[j]])*mu_element_segment[j,])%*%t(matrix(mu_element_segment[j,],ncol=(ncol(Y)-1))))}))/(sum(sapply(1:ncol(X),function(j)phi_coef[[2*j-1]]))+sum(unlist(sapply(1:ncol(X),function(j)segment_eachrow[[j]]*phi_coef[[2*j]]))))
    alpha<-apply(matrix(sapply(1:ncol(X),function(j)c(sum(phi_coef[[2*j-1]]),sum(phi_coef[[2*j]]))),ncol=2,byrow=T),2,sum)/c(ncol(X),length(segment)*ncol(X))
    ln_y <-  -((nrow(Y)*ncol(Y))/2)*log(2*pi)-(nrow(Y)/2)*det(matrix(sigma_hat,ncol=m))-tr(chol2inv(chol(matrix(sigma_hat,ncol=m)))*(nrow(Y)/2)*matrix(sigma_hat,ncol=m))
    
    ln_r <-  sum(sapply(1:ncol(X),function(j) phi_coef[[2*j-1]]*log(alpha[1]+1e-15/(phi_coef[[2*j-1]]+1e-15))+(1- phi_coef[[2*j-1]])*log((1-alpha[1]+1e-15)/(1-phi_coef[[2*j-1]]+1e-15))))
    
    ln_eta <- sum(unlist(sapply(1:ncol(X),function(j) phi_coef[[2*j]]*log(alpha[2]+1e-15/(phi_coef[[2*j]]+1e-15))+ (1-phi_coef[[2*j]])*log((1-alpha[2]+1e-15)/(1-phi_coef[[2*j]]+1e-15)))))
    
    ln_coef_segment <- sum(unlist(sapply(1:ncol(X),function(j) sapply(1:length(segment_eachrow[[j]]),function(s)phi_coef[[2*j]][s]*((1/2)*log(det(sigma_beta_element_segment[[j]][[s]])+1e-300)+(1/2)*tr(chol2inv(chol(sigma_beta_element_segment[[j]][[s]]))%*%sigma_beta_element_segment[[j]][[s]])-(segment_eachrow[[j]][[s]]/2)*log(sigma_beta)-(1/2)*tr(chol2inv(chol(diag(sigma_beta,segment_eachrow[[j]][[s]])))%*%(sigma_beta_element_segment[[j]][[s]]+crossprod(matrix(mu_element_segment[j,unlist(ifelse(s==1,{list(c(1:segment_eachrow[[j]][[s]]))},{list(c((sum(segment_eachrow[[j]][c(1:(s-1))])+1):sum(segment_eachrow[[j]][c(1:s)])))}))],nrow=1),matrix(mu_element_segment[j,unlist(ifelse(s==1,{list(c(1:segment_eachrow[[j]][[s]]))},{list(c((sum(segment_eachrow[[j]][c(1:(s-1))])+1):sum(segment_eachrow[[j]][c(1:s)])))}))],nrow=1)))))))))
    
    ln_coef_diag<- sum(sapply(1:ncol(X),function(j) phi_coef[[2*j-1]]*((1/2)*log(sigma_beta_element_diag[[j]])+(1/2)*(sigma_beta_element_diag[[j]])/sigma_beta_element_diag[[j]]-(1/2)*log(sigma_beta)-(1/2)*(sigma_beta_element_diag[[j]]+mu_element_diag[j]^2)/sigma_beta)))
    
    
    
    ELBO[itera+1] <- ln_y + ln_r + ln_eta + ln_coef_segment + ln_coef_diag
    criteria<-((ELBO[itera+1]-ELBO[itera])>tol) *( abs(test-mean((Y-X%*%beta_mean)^2))>tol)
    #criteria<-((ELBO[itera+1]-ELBO[itera])>tol)
    if(criteria){cat("Iteration:", itera-1,"th","\tELBO:",ELBO[itera],"\tELBO_diff:", abs(ELBO[itera] - ELBO[itera-1]),"\ttest:", test,"\n")}else{iteration<-itera;break}
    test<-mean((Y-X%*%beta_mean)^2)    
  }
  phi1<-lapply(1:(length(group)-1),function(j){phi_coef_pre[[j]][which(phi_coef_pre[[j]]>=.5)]<-phi_coef_pre[[j]][which(phi_coef_pre[[j]]>=.5)];phi_coef_pre[[j]][which(phi_coef_pre[[j]]<.5)]<-0;phi_coef_pre[[j]]})
  phi<- unlist(phi1)
  phi_real<-matrix(unlist(sapply(1:(p*m),function(j){A<-cbind(phi1[[2*j-1]],matrix(rep(phi1[[2*j]],segment_eachrow[[j]]),nrow=1));ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,list(A),{A[,c(1:(j%%ncol(Y)))]<-c(A[,c(2:(j%%ncol(Y)))],A[,1]);list(A)}),{A[,c(1:(ncol(Y)))]<-c(A[,c(2:(ncol(Y)))],A[,1]);list(A)})})),ncol=ncol(Y),byrow=T)
  beta_mean<-matrix(sapply(1:ncol(X),function(j)phi_real[j,]*mu_element_pre[j,]),ncol=ncol(Y),byrow=T)
  phi_coef<-phi1
  beta_var<-sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))))
  ;C<-as.numeric(crossprod(X[,j],X[,j]))*superMatrix(A,B);ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,{C[c(1:(j%%ncol(Y))),]<-C[c((j%%ncol(Y)):1),];C[,c(1:(j%%ncol(Y)))]<-C[,c((j%%ncol(Y)):1)];list(C)},{C[c(1:(j%%ncol(Y))),]<-C[c(c(2:(j%%ncol(Y))),1),];C[,c(1:(j%%ncol(Y)))]<-C[,c(c(2:(j%%ncol(Y))),1)];list(C)}),{C[c(1:(ncol(Y))),]<-C[c((2:(ncol(Y))),1),];C[,c(1:(ncol(Y)))]<-C[,c((2:(ncol(Y))),1)];list(C)})})
  
  beta_variance<-sapply(1:ncol(X),function(j){A<-matrix(sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(sigma_beta_element_segment[[j]][[s]]))))))
  ;C<-superMatrix(A,B);ifelse(j%%ncol(Y)!=0,ifelse(j%%ncol(Y)==1,{C[c(1:(j%%ncol(Y))),]<-C[c((j%%ncol(Y)):1),];C[,c(1:(j%%ncol(Y)))]<-C[,c((j%%ncol(Y)):1)];list(C)},{C[c(1:(j%%ncol(Y))),]<-C[c(c(2:(j%%ncol(Y))),1),];C[,c(1:(j%%ncol(Y)))]<-C[,c(c(2:(j%%ncol(Y))),1)];list(C)}),{C[c(1:(ncol(Y))),]<-C[c((2:(ncol(Y))),1),];C[,c(1:(ncol(Y)))]<-C[,c((2:(ncol(Y))),1)];list(C)})})
  
  sigma_hat<-(1/nrow(Y))*(crossprod(Y,Y)-crossprod(Y,(X%*%beta_mean))-crossprod((X%*%beta_mean),Y)+matrix(apply(sapply(1:ncol(X),function(j)c(unlist(beta_var[j]))),1,sum),ncol(Y)) +matrix(apply(sapply(1:ncol(X),function(j)as.numeric(crossprod(X[,j],X[,j]))*crossprod(matrix(beta_mean[j,],ncol=ncol(Y)),matrix(beta_mean[j,],ncol=ncol(Y)))),1,sum),ncol=ncol(Y))
                          +matrix(apply(sapply(1:ncol(X),function(j)crossprod(matrix(matrix(X[,j],ncol=1)%*%beta_mean[j,],ncol=ncol(Y)),matrix((X[,-j]%*%beta_mean[-j,]),ncol=ncol(Y)))),1,sum),ncol(Y))
  )
  sigma_beta<-sum(sapply(1:ncol(X),function(j){A<-matrix(phi_coef[[2*j-1]]*sigma_beta_element_diag[j],ncol=1);B<-as.matrix(ifelse(length(segment)==1,list(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))),list(superMatrix(sapply(1:length(segment_eachrow[[j]]),function(s)list(phi_coef[[2*j]][s]*sigma_beta_element_segment[[j]][[s]]))))));sum(A+phi_coef[[2*j-1]]*mu_element_diag[j]^2+tr(matrix(unlist(B),ncol=m-1))+(rep(phi_coef[[2*j]],segment_eachrow[[j]])*mu_element_segment[j,])%*%t(matrix(mu_element_segment[j,],ncol=(ncol(Y)-1))))}))/(sum(sapply(1:ncol(X),function(j)phi_coef[[2*j-1]]))+sum(unlist(sapply(1:ncol(X),function(j)segment_eachrow[[j]]*phi_coef[[2*j]]))))
  alpha<-apply(matrix(sapply(1:ncol(X),function(j)c(sum(phi_coef[[2*j-1]]),sum(phi_coef[[2*j]]))),ncol=2,byrow=T),2,sum)/c(ncol(X),length(segment)*ncol(X))
  
  
  coef_beta<-matrix(beta_mean,nrow=1)

  
  fit<-list()
  fit$Lag<-lag
  fit$Y<-Y
  fit$X<-X
  fit$gamma_pos<-sapply(1:(length(phi1)/2),function(j)phi1[[2*(j-1)+1]])
  fit$eta_pos<-c(sapply(1:(length(phi1)/2),function(j)phi1[[2*j]]))
  fit$segment<-segment_eachrow
  fit$phi<-phi_real
  fit$coef_beta<-coef_beta
  fit$iteration<-iteration-1
  fit$sigma<-sigma_hat
  fit$coef_variance <-beta_variance
  return(fit)
}

#============= Predict y_hat given X and object model====================
predict.VB_NAR<-function(object,Y,X=NULL, step_ahead=1){
  p<-object$Lag
  Y1<-as.matrix(Y)
  
  if(is.null(X))
  {
    Y<-rbind(as.matrix(object$Y),Y1)
    Y<-Y[c((nrow(Y)-nrow(Y1)-p+1):nrow(Y)),]
    X<-t(sapply((p+1):nrow(Y),function(j)c(t(Y[c((j-1):(j-p)),]))))
  }
  X<-rbind(object$X,X)
  if(step_ahead==1)
  {
    y_hat<- X[nrow(X),]%*%matrix(object$coef_beta,ncol=m)
  }else{
    y_hat<- X[(nrow(X)-step_ahead+1),]%*%matrix(object$coef_beta,ncol=m)
    for(i in 2:step_ahead){
      bb<-matrix(0,nrow=m*p,ncol=m)
      phi_idx<-object$phi
      for(j in 1:m)
      {
        if(length(which(phi_idx[,j]>0))>0)
        {
          bb[c(which(phi_idx[,j]>0)),j]<-solve(crossprod(X[c(1:(nrow(object$X)+i-1)),c(which(phi_idx[,j]>0))],X[c(1:(nrow(object$X)+i-1)),c(which(phi_idx[,j]>0))]))%*%crossprod(X[c(1:(nrow(object$X)+i-1)),c(which(phi_idx[,j]>0))],rbind(matrix(object$Y[,j],ncol=1),matrix(Y[c(1:(i-1)),j],ncol=1)))
        }
      }
      y_hat<-rbind(y_hat, X[(nrow(object$X)+i),]%*%bb)
    }
  }
  
  return(y_hat)
  
}



#============= TPR_FPR_CTR ==================================================
TPR_FPR_TCR<-function(fit,coef_beta,beta,Iteration)
{
  if(nrow(beta)!= p*m){
    stop("Inputs arguments object ae not compatible")
  }
  beta<-as.matrix(beta)
  phi_true<-unlist(sapply(1:(2*p*m),function(j)ifelse(j%%2!=0,ifelse(beta[j%/%2+1,ifelse((j%/%2+1)%%ncol(Y)==0,ncol(Y),(j%/%2+1)%%ncol(Y))]==0,0,1),list(sapply(1:length(fit$segment[[j%/%2]]),function(s)ifelse(sum(abs(beta[j%/%2,ifelse(j%/%2%%ncol(Y)==0,-ncol(Y),-(j%/%2%%ncol(Y)))][c((sum(fit$segment[[j%/%2]][c(1:s)])-fit$segment[[j%/%2]][[s]]+1):sum(fit$segment[[j%/%2]][c(1:s)]))]))==0,0,1)))) ))
  TP<-sapply(1:Iteration,function(j)sum(ifelse(abs(coef_beta[j,which(c(abs(beta[c(1:(m*p)),]))>0)])>0,1,0)))
  FN<-sapply(1:Iteration,function(j)length(which(c(abs(beta[c(1:(m*p)),]))>0))-sum(ifelse(abs(coef_beta[j,which(c(abs(beta[c(1:(m*p)),]))>0)])>0,1,0)))
  FP<-sapply(1:Iteration,function(j)sum(ifelse(abs(coef_beta[j,which(c(abs(beta[c(1:(m*p)),]))==0)])>0,1,0)))
  TN<-sapply(1:Iteration,function(j)length(which(c(abs(beta[c(1:(m*p)),]))==0))-sum(ifelse(abs(coef_beta[j,which(c(abs(beta[c(1:(m*p)),]))==0)])>0,1,0)))
  
  TPRFPRTCR<-list()
  
  TPRFPRTCR$TPR<-mean(TP/(TP+FN))
  TPRFPRTCR$FPR<-mean(FP/(FP+TN))
  TPRFPRTCR$TNR<-mean(1-TPRFPRTCR$FPR)
  TPRFPRTCR$TCR<-mean((TP+TN)/length(c(beta[c(1:(m*p)),])))
  
  TPRFPRTCR$indicaor_ture<-sum(phi_true)
  TPRFPRTCR$coef_true<-length(which(abs(beta)>0))
  TPRFPRTCR$coef_est<-mean(sapply(1:Iteration,function(j)(length(which(abs(coef_beta[j,])>0)))))
  
  return(TPRFPRTCR)
}

#========================Simulation========================================================================
Beta<-as.matrix(read.table("D:/BetaExample32m10.csv",sep=",",head=F))
m<-nrow(Beta)
p=lag<-10
Beta1<-NULL
for(i in 1:p)
{
  Beta1<-rbind(Beta1, Beta[,c(((i-1)*m+1):(i*m))])
}

table(beta==Beta1)
Data<-read.table("D:/Example32m10_1_rep100.csv",sep=",",head=F)

p=lag<-10

segment =c(m)  
#c(rep(1,m)) for NG
#c(m)        for UG
#c(3,3,4)    for m10SG 
#c(5,5,3,7)  for m20SG
phi<-matrix(0,nrow=100,ncol=length(segment)*m*p+p*m)
coef_beta=phi<-matrix(0,nrow=100,ncol=((p*m)*m))
coef_variance <-list()
mspe=mse<-NULL
sigma_hat<-matrix(0,nrow=100,ncol=m*m)
time<-proc.time()
for(k in 1:100)
{
  Y<-as.matrix(Data[-nrow(Data),c(((k-1)*m+1):(k*m))])
  Y1<-as.matrix(Data[nrow(Data),c(((k-1)*m+1):(k*m))])
  fit<-VB_NAR(Y=Y,lag=p,segment = segment)
  mspe<-c(mspe,mean((Y1-predict.VB_NAR(fit,Y1))^2))
  mse<-c(mse,mean((Y-fit$X%*%matrix(fit$coef_beta,ncol=m))^2))
  
  #phi[k,]<-fit$phi
  coef_beta[k,]<-fit$coef_beta
  phi[k,]<-fit$phi
  sigma_hat[k,]<-fit$sigma
  coef_variance[[k]]<-fit$coef_variance
}
A<-proc.time()-time
ACC<-TPR_FPR_TCR(fit,coef_beta,Beta1,100)
mean(mspe)
var(mspe)
ACC


