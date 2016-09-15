Rails.application.routes.draw do
  # MAIN INDEX
  get '/' => 'main#index'  
  # ADMIN SURVEYS
  get 'admin/new_survey'
  post 'admin/new_survey' => 'admin#new_survey'
  delete 'admin/delete_survey' => 'admin#delete_survey'


  get 'admin/survey_add_question'
  post 'admin/survey_add_question' => 'admin#survey_add_question'

  # ADMIN LOGIN LOGOUT
  get 'admin/login'
  get 'admin/logout'
  get 'admin/mainpage'

  post 'admin/login' => 'admin#login'
  delete 'admin/logout' => 'admin#logout'
  get 'admin/logout' => 'admin#logout'
    
  # ADMIN USER MANAGEMENT
  delete 'admin/delete_user' => 'admin#delete_user'
  

  # USER 
  get 'user/signup'
  get 'user/login'
  get 'user/mainpage'

  post 'user/signup' => 'user#signup'
  post 'user/login' => 'user#login'
  delete 'user/logout' => 'user#logout'

  get 'user/logout' => 'user#logout'
  
  # USER TAKING SURVEY
  get 'user/take_survey' => 'user#take_survey'    
  post 'user/take_survey' => 'user#take_survey'    

  # USER VIEWING SURVEY
  get'show_survey_result' => 'user#show_survey_result'

end
